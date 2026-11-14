# The source language of zkc: reference of the language

This document is the reference of the source language of zkc. It is one of a set:
`CORE-LIBRARY.md` gives the nine modules that the rules of this reference name,
`STANDARD-LIBRARY.md` the libraries above them, `lib/zkc/` the library in source, `programs/`
the worked programs in source, and `conformance/` the tests that an implementation must pass.
The language is designed in layers (§0.1). The inner layer, layer A, is frozen as the baseline
of the implementation: an implementation starts from it. The later layers are carried, and each
of their sections opens with a note that gives its state. A parser works from §3 and §5, a
checker from §6, an emitter from §4, §7 and §8, a library author from §2 and from
`CORE-LIBRARY.md`. Every rule is stated once. §1 to §8 state the language, §E the design of
constraint systems, §9 what the language requires of the core, §10 what
is open, and §11 how the set is checked.

Conventions. A rule carries an identifier (`HO2`). A rule that refuses a program gives the
wording of the message after **Message**; words in angle brackets are filled in by the checker.
A section or a rule that is not frozen opens with a note in italics that starts with *State*.
Appendix A lists the identifiers. "The core" is the `core` dialect and the local dialect of the
protocol level; §7.0 summarizes it.

---

## 0. Terms

| Term | Meaning | Rule |
|---|---|---|
| role | a party of a protocol, named in its roster `roles(P, V)` | §5.9 |
| holder | a role that has a copy of a named value | HO1 |
| agreement | the copies of one name at several holders are equal when those roles follow the protocol | HO6 |
| event | a statement at which information moves or randomness enters: `send`, `draw`, `sample`, an oracle send, `query`, `open`, `attempt`, an application of a protocol | EV1 |
| site | the place of one event in a definition; a number, and a name for clauses and scheme lines | EV3 |
| part | one of the core operations that one event elaborates into | EV3 |
| transcript | the values bound by events, in order | EV8 |
| participant | a role that acts inside a loop or a choice | CT1 |
| fact | something a role knows about an immutable value at a point of control: a range, a length, an order | TY4 |
| static | known at instantiation: a type, a natural or a module; a static natural is a number in every instance | SP3, TY2 |
| instance | a definition at closed static arguments; typing is defined on instances | SP7 |
| uniform, stepped | a loop whose iterations all type alike; a loop whose iterations differ in type | TY10 |
| default instance | an instance at which a public definition that no root reaches is checked | SP7 |
| vocabulary, row | the definition, in the formal library, of the types and operations that exist below the language, printed for the tools; one operation of it | NL9 |
| kernel | native code attached to a definition that has a body; an implementation, never a meaning | FN5 |
| home module | the module whose functions give a declared type its operators and its dot calls: the module that declares a record or a variant | NL5, NL6 |
| cost | the count of row applications of a function at an instance: a formula in the lengths of its inputs of run-time length | FN7 |
| opaque type member | a type member of a module parameter, typed in a generic definition as a fresh type that has only what its interface declares; that typing resolves the operators on it | SP12, NL6 |
| sort | an interface of `zkc::algebra` that only the vocabulary implements: `Group`, `Ring`, `Field`, …; the bound of a type parameter | SP3 |
| language item | a name of the core library that a rule of this reference mentions | NL10 |
| core library | the modules that hold a language item or a name that the vocabulary provides; it has the version of the language | §2.5 |
| kind | what an oracle holds and answers: a module that implements `Kind`; its shape is in its static arguments | OR1 |
| handle | the value `Oracle<K>` that names data at its holders for its reader | OR2 |
| opener, reader | the role that answers a query from the data; the role that asks | OR4 |
| claim | a row told and not yet proved: a linear value `Pending<K>` | OR5 |
| law | the uniform distribution of the type named after `draw` or `sample`; also a `law` member of an interface, an equation its implementations satisfy, and a `law` of a module, a proposition about its own definitions | TY15, SP10 |
| specification item | a `relation`, `spec def`, `spec type`, `spec protocol`, `spec` port or argument, `spec` static parameter, `spec for`, `law` | SX1 |
| scheme | the facts of one deployment of one protocol instance | SC1 |
| offline, ideal, online | a role that runs before the run; a trusted party of the run, connected by the host; every other role | SC2 |
| suite | the transcript and encoding choices of a `derived` construction: a module that implements `Suite` | SC5 |
| layout | which values a proof carries and which are recomputed, and how a value is written as units: a module that implements `Layout` | SC5, TY14 |
| proposal file | a file beside the source that completes pins, layouts and grinding bits | SC7 |
| goal | a request for a receipt: a security property of a scheme | GL1 |
| receipt | the record that a goal was proved: the statement, its hypotheses, the bound, the assumptions | GL5 |
| experiment, honest side | the game of a security property; the roles that follow the protocol in it | SX7 |
| external statement | a function, a relation, a type or a clause whose meaning is in the formal library and not in the source; a goal that uses one is reported as resting on it | NL9, GL5 |
| deployment identity | the hash of the projection that a scheme's protocol instance reaches; what proofs are bound to | §7.1 |
| admission check | a check at the host boundary before any role runs | EN2 |
| formal library | the Lean library that defines the core and the vocabulary and proves goals | — |
| canonical text | what the formatter prints | §3.6 |
| layer | a part of the language with one state of design, A to F; layer A is frozen | §0.1 |

### 0.1 Layers and state

The language is designed in six layers. A layer is *frozen* when its rules are the baseline of
the implementation that starts from them. Frozen is not certified closed: that the later layers
only add to a frozen layer, and change nothing that a program written under it means, is a
hypothesis, tested for each later layer when it is designed. A layer that is *carried* is
taken over from the earlier design of the language and not yet re-examined. Where only the
direction of a redesign is settled, the old rule stands and is marked *superseded, pending*; the
note at the head of its section states the direction. Where a frozen rule depends on a later
layer in a way that is not additive, the freeze is conditional there: those clauses are marked
in their rules as layer C or layer D. A frozen rule is amended only by a clarification: a
statement of what its text means where the text is silent, ambiguous or says two things.

| Layer | Holds | State |
|---|---|---|
| A | interaction (roles, events other than oracle events, guards, loops, applications, holders), data (types, static sizes, facts), functions, modules and interfaces, basic algebra | frozen |
| B | specification: relations, clauses, goals | carried; the statement of a property is the formal library's |
| C | schemes, Fiat–Shamir, layouts, entries | carried; the absorption schedule is pending |
| D | oracles, commitments, derived kinds | carried; a redesign is pending |
| E | constraint systems | a design of the standard library, not frozen (§E) |
| F | setup and pairing-based arguments, lattices, extractors over loops, recursion | not designed (§10.2) |

The grammar is one (§5): the productions of every layer are in it, and each production of a
later layer carries its layer. A parser of layer A reads all of them.

| Part | Rules | Layer | State |
|---|---|---|---|
| §0 Terms, §1 Principles | — | A | frozen |
| §2.1 to §2.3 Criteria, tiers, tests | B1 to B10 | A | frozen |
| §2.4 Language items | NL10 | A | frozen: the sorts and sixteen other names; the signatures of the items of `zkc::oracle`, `zkc::commitment`, `zkc::layout` and `zkc::construction` belong to layers C and D and are not frozen |
| §2.5, §2.6 Tables, tiers of constructs | — | A | frozen; the entries for the abilities of a simulator and the words of a goal are layer B |
| §3 Lexical structure, canonical text | LX1 to LX10, FM1 to FM3 | A | frozen; in the operator table of §3.5 the handles of a linear kind are layer D |
| §4 Kernel and derived forms | — | A | frozen; the lines for oracle forms are layer D, for `spec for` and `goal` layer B, for `scheme` and `entry def` layer C |
| §5 Grammar | GR1 to GR6 | A | frozen as a grammar; the meaning of a production of a later layer is that layer's |
| §6.1 Names | NL1 to NL9 | A | frozen |
| §6.2 Static parameters, instantiation | SP1 to SP12 | A | frozen |
| §6.3 Types, sizes, facts | TY1 to TY13, TY15, TY16 | A | frozen; in TY16 the collected handles and claims are layer D |
| §6.3 | TY14 | A, C | its first two paragraphs (decoding, the type on the wire) are frozen, except that the absorption of a collection with its length is layer C; the paragraphs on layouts are layer C |
| §6.4 Holders | HO1 to HO6 | A | frozen; the clauses about handles, and the lines of HO2 for oracle sends, `query` and `open`, are layer D |
| §6.5 Events and sites | EV1 to EV8 | A | frozen; the oracle send, `query` and `open` in EV1 and EV3 are layer D; a label of a site for a suite is layer C |
| §6.6 Guards and reasons | GU1 to GU4 | A | frozen |
| §6.7 Control and participants | CT1 to CT6 | A | frozen |
| §6.8 Role maps | RM1 to RM4 | A | frozen |
| §6.9 Linearity | LN1 to LN3 | A | frozen; `Pending<K>` and `open` as a use in LN1 and LN2 are layer D |
| §6.10 Oracles | OR1 to OR11 | D | carried; OR4, OR5, OR7, OR9 and OR10 are superseded, pending the redesign of claims and derived kinds |
| §6.11 Functions | FN1 to FN7 | A | frozen |
| §6.12 Specification | SX1, SX2, SX4, SX10 | A | frozen: what is specification, what is deployed, specification ports, the three judgments |
| §6.12 | SX3, SX5 to SX9 | B | carried |
| §6.13 Schemes | SC1 to SC8 | C | carried; the `commit` lines of SC5 are layer D; pending: what each step relies on in `Commitment`, `Suite` and `Layout`, and the schedule of the Fiat–Shamir step |
| §6.14 Goals | GL1 to GL5 | B | carried |
| §6.15 Entries | EN1 to EN3 | C | carried |
| §7.0 to §7.5 Elaboration | — | A | frozen for the forms of layer A, and stated for the core as it is: a stepped loop is its iterations in sequence, and each occurrence of a site is a site of the core (§7.5) |
| §7.6 Oracles | — | D | carried; superseded, pending the redesign of claims and derived kinds |
| §7.7 Specification and requests | — | B | carried |
| §7.8, §7.9 Schemes, entries | — | C | carried |
| §7.10 What the frontend keeps | — | A | frozen as a contract of the elaboration towards the later layers; events are kept with their sites, parts and iterations in the table of sites (§7.5); the members that name the views of later stages are not designed |
| §8 Generated members | — | B for `P::…`, C for `S::…` and `L::…` | carried |
| §E Constraint systems | — | E | not frozen |
| §9 to §11, Appendix A | — | — | records, not rules |

---

## 1. Principles

1. **Three places where code runs.** Inside one role: a `def`, deterministic and free of roles.
   Among the roles: a `protocol`. Outside all of them: an `entry def`, which runs whole schemes.
   A `spec` item runs nowhere.
2. **A name has holders.** `x: T @S`; several roles hold equal copies when they follow the
   protocol. Computation follows operands: a role computes what it holds the operands of, and
   nothing gives a role a value it could not form.
3. **Information moves, and randomness enters, only at events, and every event is written.** An
   event stands alone on its line. The binder of an event is its name. The names bound with
   `<-` are the transcript.
4. **A role stops at a `guard`, and acceptance is reaching the end.** A guard in a protocol names
   the roles that check, and why a failure stops. The program as written has no other way to
   reject, and no operation of the vocabulary stops.
5. **Control belongs to the roles that act in it**, and they must hold what decides it. No message
   is added to tell anyone which way a branch went.
6. **Nothing is inserted.** No send, coin, read, commitment, check or stop that the author did not
   write. What is inferred never moves information: who computes, who sends a value that one role
   holds, which roles a loop has, which role of a callee is which.
7. **A protocol is written once for all its roles and all its deployments.** Roles are parameters,
   mapped by name. Which role is offline or ideal, how the proof is built and written: these are
   lines of a `scheme`.
8. **Statement, witness and public parameters are positions, not marks.** A parameter is what an
   offline role publishes; the statement is what prover and verifier share at the entry; the
   witness is the rest of what the prover holds.
9. **Specification is erasable.** What is deployed is a projection of the source: what the steps
   of the tool run. No specification item, goal, kernel or specification-only member of a module
   is in it, so changing one changes no role program, no proof byte and no identity of a proof.
   No law, proof, goal or hypothesis selects executable code.
10. **One word, one meaning; one fact, one place; one spelling per type.** What the roster, the
    holders, the binder or the signature determines need not be written. An annotation that
    restates what the rules compute is accepted and removed by the formatter; a wrong one is an
    error.
11. **Sizes are static.** A size is a number in every instance, and typing is defined on
    instances. The shape of an oracle is a size. What a role knows about a run-time value is a
    fact, made by a guard or by the condition of a choice.
12. **A small surface with a written elaboration.** Six statements and eight declaration heads
    organize the surface. Every other form has an elaboration into them (§4, §7).
13. **Syntax is for what is not a value.** A form is syntax only when the compiler must see in it,
    as one written thing, a role, a binder, a site, a type, a block, a stop with its reason, a
    public coin, a restart point or a custody. Everything else is a name of a library (§2).
14. **Meaning and speed are two statements.** The meaning of a definition is its body. A kernel is
    an implementation attached to it, and that the kernel computes the body is a named assumption.
15. **The compiler refuses what it cannot project**, at the line, in the words of the source,
    with the chain of instantiations that led there.
16. **Nothing unchecked is reported as accepted.** A tool lists what it did not check: a
    statement that rests on the formal library, a row whose signature it took as written, a
    definition it resolved for names only.

---

## 2. Language, tables, vocabulary, libraries

This section says where a construct belongs. It decides every later addition.

### 2.1 Criteria

**B1. Syntax is for what is not a value.** A construct is syntax only if one of its operands is
a role, a binder, a site, a type, a declaration or a block of statements, or if it is a place
where information moves, randomness enters, a role stops or control divides. A construct whose
operands and result are values is a name.

**B2. A fact that the compiler acts on is one written thing.** When projection, the numbering
of sites, a step of the tool, or a message at the line needs a fact, the fact is one statement,
one line or one declaration. It is never recovered from a pattern of several calls.

**B3. No privileged signatures.** The fixed table selects a function for a symbol; it has no
typing rule of its own. Every typing power that a built-in operation uses is on this list, and
a declaration bound to a row has the same list: overloading by the sort of an operand; a domain
that the facts of the caller discharge (TY4); a result range; a result type computed from
static arguments.

**B4. The compiler knows library names from one table.** A library name that a rule of the
language mentions is a *language item*. Items are listed in §2.4, are declared in the core
library, and the core library has the version of the language.

**B5. A row is what cannot be written.** A row is an operation of the signature of a sort, of a
reserved type or of a sealed type of the vocabulary, or an operation of the world (entropy, an
asset). Whatever can be defined from those is defined in source.

**B6. Meaning and speed are two statements.** The meaning of a definition is its body. A kernel
is an implementation attached to it. That the kernel computes the body is a named assumption:
listed in each receipt that rests on it, tested at every build by running both, proved later
without changing any client. No row can stop: a role stops at a `guard`, and a decoder returns
`Option`.

**B7. Composition, not enumeration.** What is made of parts is a module with static parameters:
a Merkle tree over a hash, a suite over a hash and a field, a commitment over a kind. The
vocabulary holds the parts, never one identity per combination.

**B8. The prelude is what the syntax and the fixed tables produce or require.** In scope without
`use` are the names that the syntax and the fixed tables of the language produce or require: the
sorts, as the closed table they are; the types that a statement of the language produces,
together with their eliminators; `byte` and `length`. Frequency is not a reason: nothing enters
the prelude because it is used often.

**B9. Specification mathematics lives where its theorems live.** A function that runs nowhere
and whose theory exists in the formal library is bound with `external`. A formula over values
is written in source.

**B10. One spelling per type.** A type has one notation, fixed by its sort. A second spelling of
the same operation on the same type is not offered, by the table or by a library.

### 2.2 Tiers

| Tier | Holds | To add one costs | Trust it carries | What a proof sees |
|---|---|---|---|---|
| (a) language, kernel form | the six statements and eight heads of §4.1, the bindings `primitive`, `asset`, `external` | a production, a checker rule, a core operation, its meaning in the formal library, a case in every step and in every theorem about the core | the model of the formal library is the definition; the frontend's elaboration is tested or validated | one core operation with its meaning |
| (a′) language, derived form | every form of §4.2 | a production, one elaboration rule, tests; nothing in the core | that the elaboration preserves placement, outcomes and observations | only what it elaborates into |
| (b) fixed table | operators, mathematical forms, reasons, reserved types, size operators, sorts, words of a goal, the rows of §7.4 | one table line and the typing it needs from the list of B3; a change of the language | none of its own: a symbol means a function | the function |
| (c) language item | a name of the core library that a rule mentions (§2.4) | one line of the item table and the compiler code that reads it; the name and its signature are frozen with the language version | that of its tier (d) or (e) | that of its tier |
| (d) vocabulary row | operations of sorts, of reserved and sealed types, of the world; properties and models as entries | the signature and meaning in the formal library, the printed vocabulary, a kernel per target, cost data, tests | the kernel computes the meaning; listed in receipts | a function of the formal library, or, generically over a sort, the laws of the sort |
| (e) source | definitions, records, interfaces, protocols, relations, schemes | the code; a changed definition changes the deployment identity of what reaches it | none beyond the language; with `#[kernel]`, that the kernel computes the body | the body; through an interface, its laws |
| (f) formal library | properties, models, experiments, bounds, mathematics with a theory there | definitions and theorems of the formal library | its definitions are part of every statement that names them and must be read; its proofs are checked | the object of the formal library; source sees a header |
| (g) generated member | records and functions that one declaration determines (§8) | a line of §8 and generator code | that of the generator | records by site; functions by their definition in §8 |

Tier (c) is a mark on a declaration of tier (d) or (e), not a place of its own.

### 2.3 Tests

Ask in order. The first test that applies gives the tier.

| # | Question | Yes |
|---|---|---|
| T0 | Is it a function of one declaration (a protocol, a scheme, a type, a layout) and of nothing that an author chooses? | (g) generated |
| T1 | Does it take an operand that is not a value, or mark a place where information moves, randomness enters, a role stops or control divides? | (a) language. *Kernel* when the core has one operation for it and it states a fact that only the author knows (B2). *Derived* when a written elaboration into kernel forms preserves placement, outcomes and observations and its errors can be reported in the words of the source |
| T2 | Its operands are values, but typing it needs a power of B3 applied to a type that has literals, widening or narrowing, or it is wanted as a symbol? | (b) a reserved type or a table entry. The function it selects is classified by T4 to T6 |
| T3 | Does a rule of the language mention its name? | mark (c); continue with T4 to T6 |
| T4 | Does it run nowhere? | a formula over values: (e), a `spec def` or a `relation`. A notion whose theory is in the formal library: (f), bound with `external` or named as a vocabulary entry |
| T5 | Can its meaning be written as a body over the lower tiers? | (e) source. Attach a kernel when interpreting the body is too slow and the body cannot stop |
| T6 | Otherwise | (d) a row. Say which: an operation of a sort, of a reserved or sealed type, or of the world |

Four secondary rules.

- *Could it be a library definition over a smaller language?* For a form that T1 puts in the
  language, name what the compiler must see in it as one written thing (B2): a site, a role, a
  stop with its reason, a public coin, a restart point, a custody. If nothing, it is a library
  definition. If something, that is the reason the form exists; the last column of §4 names it.
- *When does a table grow?* A symbol is added when its function already exists by T5 or T6, the
  symbol is the notation of the literature for it, and its typing needs no power outside B3.
  Each addition is a change of the language.
- *When is a type reserved?* When it has literals, takes part in widening or narrowing, or
  occurs in the typing rule of a kernel statement. Otherwise it is a record, an alias or a
  sealed type of the vocabulary.
- *Member or free function?* An operation whose static argument cannot be inferred from a value
  argument is a member reached through the type or module (`G::generator()`, `F::Order`). An
  operation on values is an operator when the table has one, a free function otherwise.

### 2.4 The language items

**NL10.** The rules of this reference mention these names of the core library and no other
library name: the sorts, which are one closed table (§2.5), and the names below them. Each is
declared `pub` in the module given, with the signature that `CORE-LIBRARY.md` gives; the
compiler finds it there and identifies it by that declaration, so a declaration of the same name
elsewhere is another thing. A module outside the core library does not declare a name of the
prelude (NL4). The five functions of the fixed table, `sum`, `product`, `all`, `any` and `inner`,
are not names of the prelude in this sense: they have no declaration, a module may declare a
name equal to one of them, and the declaration hides the function in that module, as a local
name does. The core library has the version of the language. The table is not a fixed count:
it grows when a sort is added to the table of sorts, or when a step of the tool or a generator
reads a declaration by name, and for no other reason.
**Messages:** "the language item `<Kind>` is not declared as a public interface of
`zkc::oracle`"; "`<length>` is a name of the prelude; a module does not declare it".

| Item | Module | Kind | The rules that read it |
|---|---|---|---|
| `length` | `zkc::prelude` | function | TY4, TY8, TY9 |
| `Option` | `zkc::option` | variant | TY14, SC5, SX9, §8 |
| the sorts: `Group`, `Ring`, `PrimeOrderGroup`, `Field`, `PrimeField`, `ExtensionField`, `TwoAdicField` | `zkc::algebra` | interfaces | SP3, SP7, NL6, TY1, TY6, TY11, TY12, TY14, TY15 |
| `Kind` | `zkc::oracle` | interface | OR1, OR3, OR4 |
| `Rows` | `zkc::oracle` | interface | OR9 |
| `Linear` | `zkc::oracle` | interface | OR8, NL6 |
| `Derived` | `zkc::oracle` | interface | OR10 |
| `Oracle` | `zkc::oracle` | sealed type | TY1, OR2 |
| `Pending` | `zkc::oracle` | sealed type | TY1, OR5, LN1 |
| `data` | `zkc::oracle` | function | OR2, HO1 |
| `pending` | `zkc::oracle` | function | OR5 |
| `lower` | `zkc::oracle` | function | OR10 |
| `Commitment` | `zkc::commitment` | interface | SC5 |
| `Hash` | `zkc::hash` | interface | SC5 |
| `Layout` | `zkc::layout` | interface | TY14, SC5, SX9 |
| `canonical` | `zkc::layout` | module | SC5 |
| `Suite` | `zkc::construction` | interface | SC5 |

Besides the items the compiler knows four things that are not library names: the fixed function
names of a home module (`add`, `sub`, `mul`, `div`, `rem`, `pow`, `neg`, `equal`, `at`, `zero`,
`one`; NL6); `Self` in an interface (SP8); the entries of the vocabulary of kind `property` and
`model`, with what GL3 reads of each (GL1), and the default representative of each sort (SP7);
and the rows and the operations of §7.4, which it applies with no source declaration between.

### 2.5 The fixed tables, and the three libraries

The fixed tables of the language, each closed and each changed only with the language:

| Table | Where | Entries |
|---|---|---|
| reserved types | TY1 | `bool`, `nat`, `index<n>`, `nonzero<F>`, `[T; n]`, `[T]`, tuples, `rational` |
| operators | §3.5 | `+ - * / % ^ ++ == != < <= > >=`, `and`, `or`, `not`, prefix `-`, indexing, slices |
| mathematical forms | §3.5 | `∑ ∏ ∀ ∃`, `⟪ ⟫`; their ASCII spellings `sum`, `product`, `all`, `any`, `inner` |
| size operators | TY2 | `+ - * / ^`, `log2( )` |
| reasons | GU3 | `reject`, `abort`, `refused`, `exhausted` |
| sorts | SP3 | `Group`, `Ring`, `PrimeOrderGroup`, `Field`, `PrimeField`, `ExtensionField`, `TwoAdicField` |
| abilities of a simulator | SX6 | `coins`, `programming`, `trapdoor` |
| words of a goal | GL2 | the stages `written`, `committed`, `constructed`, `serialized`; `fixed`, `adaptive`; `hidden`, `observed`; `residual` |
| rows and operations applied without a declaration | §7.4 | 26 rows of the vocabulary, on the sorts, on `nonzero<F>` and on collections of elements of a sort; the function members of the sorts; the 25 operations that the core owns, on the other reserved types |

*The core library* is the set of modules that hold a language item or a name that the vocabulary
provides: `zkc::prelude`, `zkc::option`, `zkc::algebra`, `zkc::oracle`, `zkc::commitment`,
`zkc::hash`, `zkc::layout`, `zkc::construction`, `zkc::security`. It cannot change without this
reference changing. *The standard library* holds no item: a module of it can be replaced by
another with the same signatures and no rule notices. A *protocol library* declares a `protocol`.

### 2.6 Where each construct is, and why

What the compiler sees in a form as one written thing is the reason it is syntax.

| Construct | Tier | What the compiler must see in it |
|---|---|---|
| `send e to V` | kernel | its roles; a site |
| `draw L from V to P` | kernel | a public coin: one operation that the Fiat–Shamir step replaces; a list of receivers |
| `sample L` | kernel | a private coin of one role; a site |
| `send … as oracle<K>` | kernel | a handle with a placement; the number of oracles of a loop |
| `open` | kernel | the consumption of linear claims of several kinds in one operation |
| `attempt` | kernel | the point from which `retry` restarts |
| `guard @S c else ρ` | kernel | the roles that stop, the reason, the narrowing |
| `if`, `match`, `for`, `return` | kernel | a block; the participants |
| `query … deferred` | derived | one exchange of rows and a claim at each of two roles; the opener, at the line |
| `query` | derived | a deferred query and an `open` under one site |
| `send e to V, W`; `mut`, `:=`; `for x in xs`; `if … then … else`; `and`, `or` | derived | as §4.2 states |
| `for … collect (ys = e)` | derived | that a loop that produces values keeps one type for its state |
| comprehensions, `∑ ∏ ∀ ∃` | derived, table | a binder |
| the range of a loop | syntax | part of the domain of `for`, of a comprehension, of a binder form; there is no range value |
| `struct`, `enum`, `linear struct` | kernel heads | data; "used exactly once", which no signature can say |
| `relation R(x…; w…)` | derived head | the split, from which the deciding role is computed |
| `oracle def` | derived head | one row expression, from which the positions read are derived and checked |
| `interface`, `law`, `section`, `module`, `use` | heads | names and static dispatch |
| the clauses of `spec for` | syntax | ports, sites, loop indices and roles, typed in the scope of the protocol |
| `scheme` and each of its lines | syntax | sites, roles, kinds and modules: no operand is a value |
| `goal` | head | a property applied to a scheme; the language has no top-level values |
| `entry def` | head | that only an entry runs a scheme |
| `primitive`, `asset`, `external`, `#[kernel]`, `#[site]` | bindings and marks | the name of something outside the language; the name of a site |
| `nonzero<F>`, `index<n>`, `rational` | reserved types (b) | narrowing by a guard, widening, literals, laws, decoding |
| `byte` | source (e) | nothing: an alias of `index<256>` in the prelude |
| `length` | item (c), a row | a term of the fact calculus |
| `Oracle<K>`, `Pending<K>`, `data`, `pending`, `lower` | items (c), rows | what `send … as oracle`, `query … deferred` and `open` produce and consume |
| `Kind`, `Rows`, `Linear`, `Derived`, `Commitment`, `Hash`, `Layout`, `Suite` | items (c), source | interfaces whose members a rule or a step applies by name |
| a primitive kind (`table`), a commitment scheme, a suite, a layout | source (e) | nothing: modules that implement the item interfaces |
| a constraint system: an AIR, R1CS, a Plonkish table, a layered circuit | source (e), standard library | nothing: a module that implements an interface of `zkc::constraint` (§E) |
| hashes, permutations, fields, groups, pairings | rows (d) | — |
| polynomial evaluation, FFT, batch inversion, a multi-scalar multiplication | source (e) with a kernel; the last is the meaning of `⟪points, scalars⟫` | — |
| `soundness`, `random_oracle`, … | formal library (f), named as vocabulary entries | what GL3 checks of a goal |
| `P::Run`, `S::Statement`, `L::write<T>`, structural `==` | generated (g) | — |
| function types, function literals, a `fold` that takes a function, `distribution`, `affine`, user-defined notation, a second spelling of group operations | not in the language | a loop, a comprehension or a binder form writes each; a draw of bytes and a function replaces a source distribution |

---

## 3. Lexical structure

### 3.1 The lexer

The lexer is the following procedure. Its output is a sequence of tokens with `NEWLINE`, `INDENT`
and `DEDENT`.

**LX1. Text.** A source file is UTF-8 text in Unicode Normalization Form C. A line ends at LF or
at CR LF. The properties of characters that this section names (`XID_Start`, `XID_Continue`,
Normalization Form C) are those of one version of Unicode, which an implementation pins and
states; the tests of this reference are written against Unicode 17.0.0. **Message:** "a lone
carriage return is not a line end".

**LX2. Lines.** A line that is empty or holds only spaces and a comment produces no token,
whatever its indentation. A *logical line* starts at the first other line read while no bracket
is open, and ends at the first line end at which no bracket is open; then `NEWLINE` is produced.
Brackets are `( )`, `[ ]`, `{ }`, `⟪ ⟫` and static brackets (LX5). A line end inside a bracket
is ignored, and the lines that continue a logical line have any indentation. A logical line does
not continue after an operator. **Message:** "the line ends inside an expression; a logical line
continues only inside brackets".

**LX3. Comments and tabs.** A comment starts with `//` outside a string and ends at the end of
the line. There is no block comment. A tab stands only in a comment. **Message:** "a tab is not
indentation".

**LX4. Indentation.** The indentation of a logical line is the number of spaces before its first
token. The first logical line of a file has indentation 0. A logical line indented by exactly
four spaces more than the one before it opens a *suite*: `INDENT` is produced. A logical line
indented less closes one suite per four spaces: one `DEDENT` each; its indentation is then that
of an enclosing suite. The end of the file closes every open suite. **Messages:** "a suite is
indented by four spaces, not <n>"; "dedentation must match an enclosing suite".

**LX5. Longest match, and `<`.** At each position the longest token of §3.2 is taken: `a<=b` is
`a <= b`, `a<-1` contains the token `<-`. One exception: inside a static bracket that is the
innermost open bracket, `>=` is not formed, so that `T<n>= e` closes the bracket.
`<` *opens a static bracket* when the token before it is an identifier or a word and touches it
(no space between them), and when the token before it is the word `section`. Every other `<` is
the comparison. `>` *closes a static bracket* exactly when a static bracket is the innermost open
bracket; every other `>` is the comparison. So a comparison is written with a space before `<`,
and inside static brackets a comparison is written in parentheses. **Message:** "write `a < b`
for a comparison; `<` touching a name opens static arguments".

**LX6. Identifiers.** An identifier is a character of `XID_Start` or `_`, followed by characters
of `XID_Continue`, at most 128 bytes long, and not a reserved word. The two properties are
those of the version of Unicode that LX1 names. `_` alone is the wildcard.
The characters of the Unicode blocks Mathematical Operators, Supplemental Mathematical Operators
and Miscellaneous Mathematical Symbols A and B are never identifier characters.

**LX7. Strings.** `"…"` holds printable ASCII (U+0020 to U+007E) without `"` and `\`; there is no
escape. `//` inside a string is text. A string is not a value: it stands only where §5 writes
`String`. A byte string is `b"…"` (the same characters, one byte each) or `hex"…"` (an even number
of hexadecimal digits of either case). **Message:** "hex\"...\" holds an even number of
hexadecimal digits".

**LX8. Numbers.** A number is decimal digits without a leading zero (`0` itself excepted). It has
no largest value. A name does not touch a number. **Message:** "`0x…`: numbers are decimal and a
name does not touch a number".

**LX9. Reserved words.** A reserved word (§3.3) is never an identifier. **Message:** "`<w>` is a
reserved word".

**LX10. Mathematical forms.** `∑ ∏ ∀ ∃ ∈ ⟪ ⟫` are tokens. Every other character of the blocks
named in LX6 is refused. A form has an ASCII spelling, a call of a function of the fixed table
(§3.5), for a keyboard without the symbols. **Message:** "`<c>` is not in the table of mathematical forms
(∑ ∏ ∀ ∃ ∈ ⟪ ⟫)".

### 3.2 Tokens

| Token | Form |
|---|---|
| Identifier | LX6 |
| Number | LX8 |
| String, ByteString | LX7 |
| Punctuation | `( ) [ ] { } , : ; . .. :: @ # _ = := <- -> < >` |
| Operators | `+ - * / % ^ ++ == != < <= > >=` and the words `and`, `or`, `not` |
| Mathematical forms | `∑ ∏ ∀ ∃ ∈ ⟪ ⟫` |

**`;`** has two uses: it separates the element type from the size in `[T; n]` and the element from
the count in `[v; n]`; and it separates the statement parameters of a relation from its witness
parameters, at the definition and at every application. Lists are separated by `,`.

### 3.3 Reserved words

```text
module  use  pub  as  section  interface  type  struct  enum  def  protocol  relation
scheme  goal  spec  roles  where  mut  guard  if  then  else  match  case
for  in  return  send  draw  sample  query  open  attempt  and  or  not  true  false
bool  nat  index  nonzero  rational  primitive  asset  external  sites
```

Forty-seven words. `byte`, `length` and the names of the sorts are names of the prelude (NL4),
not reserved words.

### 3.4 Contextual words

A contextual word has its meaning only in the position named; elsewhere it is an identifier. An
expression never continues with an identifier, so a contextual word after an expression ends it.

| Word | Position |
|---|---|
| `entry`, `oracle` | before `def` at the start of a declaration |
| `oracle` | after `as` in a send |
| `linear` | before `struct`; as a bound of a static parameter |
| `partial` | at the start of a member of an `interface` |
| `law` | at the start of a member of an `interface`; at the start of an item of a module or of a section |
| `Self` | in a signature of an `interface`: the implementing module |
| `from`, `to` | in a `send` or a `draw`, after the payload or the type; `from` also after the handle of a `query` and in a `retry` line; `to` also in a `reduces` clause |
| `at` | after the handle of a `query` or of a claim; in an `invariant` or `through` clause; in a `grind` line; at the start of the row line of an `oracle def` |
| `deferred` | at the end of a `query` |
| `collect` | in the head of a `for` |
| `with` | in a record update; in a `commit` line |
| `private` | after the holders of a port |
| `site`, `kernel` | inside `#[ … ]` |
| `reject`, `abort`, `refused`, `exhausted` | after `else` in a `guard` |
| `requires`, `ensures`, `invariant`, `reduces`, `proves`, `through`, `knowledge`, `zero_knowledge`, `charge` | at the start of a clause of `spec for` |
| `by`, `using`, `coins`, `programming`, `trapdoor` | inside a `knowledge` or `zero_knowledge` clause; `by` also in `samples derived by` and `recover … by` |
| `prover_key`, `verifier_key` | as the name of an argument in a `commit` line |
| `written`, `committed`, `constructed`, `serialized`, `fixed`, `adaptive`, `hidden`, `observed`, `residual` | as the value of an argument of a `goal` |
| `construction`, `prover`, `offline`, `ideal`, `context`, `commit`, `pin`, `grind`, `retry`, `samples`, `layout` | at the start of a line of a `scheme` |
| `derived`, `interactive`, `authored`, `bits` | inside a `construction`, `samples` or `grind` line |
| `carry`, `recover` | at the start of a line under `layout` |

`Self` and the words of a goal stand where the grammar has a `Name` or a `Path`; the checker reads
them (SP8, GL2).

### 3.5 Operators and mathematical forms

The table is fixed. A library adds no symbol, no precedence and no bracket; there is no
declaration of notation.

| Level | Operators | Association | Operands |
|---|---|---|---|
| 1 (loosest) | `or` | left | `bool`; the right operand is evaluated only when needed |
| 2 | `and` | left | `bool`; the right operand is evaluated only when needed |
| 3 | prefix `not` | — | `bool`; `not a == b` is `not (a == b)` |
| 4 | `==` `!=` `<` `<=` `>` `>=` | none; comparisons do not chain | `==`, `!=`: every data type; the others: naturals, and `rational` |
| 5 | `+` `-` `++` | left | groups (a ring is one, and so is a field), naturals, `rational`, sized collections of group elements, handles of a linear kind (layer D); `++` on collections |
| 6 | `*` `/` `%` | left | rings (a field is one); `element * scalar` on a group, the scalar on the right; naturals; `rational`; `collection * scalar`; `handle * scalar` (layer D); `/` on a field takes a `nonzero` divisor; `%` on naturals only |
| 7 | prefix `-` | — | groups, `rational`; `-x^2` is `-(x^2)` |
| 8 (tightest) | `^` | right; the exponent is an operand of level 7 | `ring ^ natural` (a field is a ring), `natural ^ natural`; a `rational` to an integer, as in `2^-128` |

What these operators give on operands of type `nonzero<F>` is stated in TY6.

Postfix forms bind tighter than every operator: a call `f(…)`, static arguments `f<…>`, a field
`.name`, a tuple position `.0`, an index `[i]`, a slice `[a..b]`, a path `::`.

**Group notation is additive, and the scalar stands on the right** (B10): `g * r`, `a + u * c`,
the literal `0`, `∑`, `⟪g, a⟫`. A ring is a group whose scalar is itself, so it has these and
`*`, `^` by a natural, `∏` and number literals besides; a field is a ring and has `/` as well.
On a ring `x * y` is the multiplication of the ring. There is no multiplicative spelling of a
group and no `scalar * element`. **Messages:** "`<r * g>`: the scalar stands on the right of the
point: write `<g * r>`"; "`^` is not defined for the group `<G>`: group notation is additive;
write `<g * r>`".

**Mathematical forms.** They are expressions like any other. Each is the fold of an operator, so
that a type which has the operator has the form and the two cannot disagree.

| Form | Is | ASCII spelling | Extends |
|---|---|---|---|
| `∑ x ∈ D, e` | the values of `e` in the order of `D`, added with `+`, starting from `0` | `sum([e for x in D])` | as far to the right as possible: its body `e` is an `Expr` |
| `∏ x ∈ D, e` | the same with `*`, starting from `1` | `product(…)` | the same |
| `∀ x ∈ D, e` | the same with `and`, starting from `true`; every element is evaluated | `all(…)` | the same |
| `∃ x ∈ D, e` | the same with `or`, starting from `false`; every element is evaluated | `any(…)` | the same |
| `⟪a, b⟫` | `∑ i ∈ 0..n, a[i] * b[i]` for two collections of `n` elements | `inner(a, b)` | between its brackets |

`D` is a range `a..b` or a collection, as in a comprehension. A binder form is a primary
expression, so it may stand as the last operand of an operator (`claim == ∑ v ∈ values, v`); to
continue after its body it is parenthesized (`(∑ v ∈ values, v) + 1`). `sum`, `product`, `all`,
`any` and `inner` are in scope everywhere and have no declaration: `sum(xs)` is `∑ x ∈ xs, x`.
In `⟪a, b⟫` the points come first and their scalars second.

**The function an operator means (NL6).** An operator or a mathematical form on a reserved type or
on a type of a sort has the meaning of the vocabulary: the row of §7.4. On a type declared in a
module it is the function of the fixed name below in that module, the *home module* of the type,
selected by the type of the left operand (of the operand, for prefix `-`; of the indexed value,
for `[ ]`; of the elements, for a binder form). On an opaque type member of a module parameter
it is the member of that name that the interface of the parameter declares (NL6, SP12).

| `+` | `-` | `*` | `/` | `%` | `^` | prefix `-` | `==` | `xs[i]` | `∑` | `∏` |
|---|---|---|---|---|---|---|---|---|---|---|
| `add` | `sub` | `mul` | `div` | `rem` | `pow` | `neg` | `equal` | `at` | `add` and `zero` | `mul` and `one` |

`!=` is `not` of `==`. `==` on a declared type without `equal` is structural (TY12). `∀` and `∃`
apply to `bool`. `<`, `<=`, `>`, `>=`, `++`, `and`, `or`, `not` have no function. The named
functions stay callable.

### 3.6 Canonical text

The canonical text of a program is what the formatter prints. The formatter changes no meaning:
it prints the same tokens except for the annotations of FM2.

**FM1. Layout.** Four spaces per suite. One space on each side of a binary operator except `^`,
`..` and `::`; none between a name and its static bracket; one after `,` and after `:`; none
inside brackets. One blank line between top-level items. A logical line longer than 100
characters is broken inside its outermost bracket, after a `,`, with the closing bracket on its
own line; a line without such a place stays. Roles in `@( … )`, in a roster order; one role is written without
parentheses. A body that is one expression is printed as an expression body (GR1).

**FM2. Annotations.** For each annotation: when it is redundant (accepted, and removed by the
formatter), when it is wrong (an error), and when it is kept.

| Annotation | Equal to the computed value means | Redundant | Wrong | Kept |
|---|---|---|---|---|
| `@S` on the binder of `=` or `mut` | `S` and the holders of the expression (HO2) are the same set of roles | when equal | when `S` is not a subset | when `S` is a proper subset: it restricts |
| `from p` on a `send` | `p` is the only role that holds the payload and is not a receiver | when so | when `p` does not hold the payload or is a receiver | when several roles could send |
| `from o` on a `query` | `o` is the only holder of the handle's data | when so | when `o` does not hold the data | when the data has several holders |
| `#[site(x)]` | the binder of the event is the single name `x` | when so | when the binder is another single name | when the binder is a pattern, or the event is an `open` |
| a role-map entry `O = P` | `O` and `P` are the same name | when so | when `P` is not a role of the caller, or the map is not injective | when the names differ |
| `else reject` on a guard | `reject` is the default reason | always | — | never |
| `@R` on `reduces` or `proves` | `R` is the only role that can decide the clause (SX6) | when so | when `R` cannot decide it | when several roles can |
| `-> ()` on a `def` | the result is the empty tuple | always | — | never |
| a binder `_ <-` or `x <-` on an application without results | — | `_ <-` always | — | a name: it names the site |

**FM3. Never changed.** The roles of a `guard` in a protocol body (GU2); a type annotation on a
binder (typing is defined on instances, so the formatter cannot know that it is implied); the
line `prover P` (SC3); static arguments, written or omitted; the choice between a mathematical
form and its named function.

---

## 4. Kernel and derived forms

### 4.1 Kernel forms

The surface has six statements and eight declaration heads. A form is in the kernel when the core
has one operation or one record for it and the form states a fact that only the author knows.

| Kernel statement | Core operation | The author's fact |
|---|---|---|
| `x @S = e` | `core.at`: one for each local operation of each computing role; in local code the operations of the local dialect | what is computed; `@S` only to restrict |
| an event: `x <- send`, `draw`, `sample`, an oracle send, `attempt`, an application; `open` | `core.exchange`, `core.draw`, `core.sample`, `core.oracle_send`, `core.attempt_number`, `core.apply`; `core.oracle_open` | that information moves or randomness enters here, and between whom |
| `guard @S c else ρ` | `local.guard`: in a protocol body once per role, each in a `core.at` of that role | who checks, and why a failure stops |
| `if` / `match` | `core.choose`; `local.if`, `local.match` | the branch |
| `for` | `core.repeat`; `local.loop` | the repetition |
| `return` | `core.return`; `local.yield` | the outputs |

| Kernel declaration | Core record | Why it is its own head |
|---|---|---|
| `module`, `use` | none: names | — |
| `type`, `struct`, `enum` | `core.record`, a variant declaration, a nominal type | data |
| `def` | `func.func` | local code: deterministic, free of roles, never opened by a step |
| `protocol` | `core.def` | a process: events, sites, holders |
| `interface`, `module M: I` | none: static dispatch, and one obligation per law and implementing instance; one per `law` of a module | the only abstraction over definitions; a sort is an interface that the vocabulary implements |
| `spec for P:` | `core.contract` | erased; typed against the protocol |
| `scheme` | `core.declaration` | the facts of a deployment |
| `goal` | `core.claim` | which receipts must exist |

Bound to something outside the language: `= primitive("row")` (a row of the vocabulary),
`= asset(name)` (the naturals and the data of an asset of the project), `= external("name")` (the formal library), and the mark
`#[kernel("name")]` on a `def` with a body (an implementation; NL9, FN5).

### 4.2 Every other form

Each form below is in the grammar and is defined by the elaboration given; §7 gives the result in
the core. None has a rule of its own beyond the section cited.

| Form | Elaboration into the kernel |
|---|---|
| `section <A> where (W):` | `A` and `W` are prepended to every member |
| `relation R(x…; w…): e` | `spec def R(x…, w…) -> bool: e`, with the split between statement and witness parameters kept by the frontend (§7.2); a `where` on the head is the `where` of that function |
| `proves R` | `reduces R to true` |
| `send e to V, W` | one `send` with one site and one part per receiver, in the order written |
| `mut x`, `x := e` | `x` becomes a carried value of each enclosing `for` that updates it and a result of each arm of an `if` or `match` that updates it; an update rebinds |
| `for i in a..b` | a repetition with count `b - a` and the index as a value |
| `for x in xs` | `for i in 0..length(xs)` with `x = xs[i]`; `xs` is evaluated once |
| `for … collect (ys = e):` | the loop, and afterwards `ys` bound to the collection of the values of `e` at the end of each iteration, in order (TY16) |
| `if c: A else if d: B else: C` | `if c: A else:` with the suite `if d: B else: C` |
| `if c: A else: B` | `match c` with the arm of `false` first |
| `if c then a else b` | a local choice whose arms are the two expressions |
| `if c` with `c` a static condition, as a statement or an expression | the arm taken at the instance; the other arm is not typed and leaves nothing (TY9) |
| `a and b`, `a or b` | `if a then b else false`; `if a then true else b`; each is typed as that `if`, so the right operand has the facts of the left operand, or of its negation (TY9); the boolean operation of the core when neither operand can stop |
| `[e for p in D]`, `[e for p in D if c]` | a collection over the domain `D`, elements in the order of `D`: a loop that collects (§7.4) |
| `∑ ∏ ∀ ∃`, `⟪a, b⟫`; `sum(xs)`, … | the fold of §3.5 over the comprehension: the row of §7.4 on a type of a sort, a loop that carries the accumulator on naturals and `bool`, a loop over `add` from `zero()` (`mul` from `one()`) on a declared type |
| an operator on a declared type | the call of the function of §3.5 |
| `xs + ys`, `xs * a`, `xs ++ ys`, `xs[i]`, `xs[a..b]`, `[v; n]` | applications of the collection rows and of the sequence operations of the core (§7.4) |
| a pattern binding | projections; for a linear record, its consumption |
| `T{f}` | `T{f = f}` |
| `{r with f = v}` | a construction of the record type of `r` from the fields of `r` and `v` |
| a role map by name | the total map from the callee's roles to the caller's, an attribute of `core.apply` |
| `(rows, c) <- query h from o at ps deferred` | one `send` of `[K::answer(data(h), p) for p in ps]` from the opener `o` to the reader, and `c = pending(h, ps, rows)` at each of the two, under one site (§7.6) |
| `query h at ps` (not deferred) | `(rows, c) <- query h at ps deferred`, then `open c`, as two parts of one site |
| `open h at p == v` | `open pending(h, p, v)` |
| `send … as oracle`, `open` on a derived kind | applications of the kind's `Send` and `Open` protocols (§7.6) |
| an instance of an `oracle def`, and a `query` of it | a record of the parent handles and the captures; one block over its parents (§7.6) |
| `e.m(a)` | `H::m(e, a)`, `H` the home module of the type of `e` |
| `C(args)` on its own line | `_ <- C(args)`: an application without results needs no binder (EV1) |
| `x = e` with `e` a static term; `nat N = e` in a module or a section | a static name: it stands for the number `e` evaluates to (TY2) |
| a `law` of a module | a specification-only function without a caller, and one obligation record of the module (SP10) |
| `entry def` | a host entry: a function over the generated members of schemes (§7.9) |

### 4.3 What the kernel claim is

The claim is one of coverage: every form of §4.2 has a written elaboration (§7) whose result the
core's admission accepts and which preserves placement (which role computes), outcomes (returning,
or stopping with a reason, in the same order) and observations (what each role sends and
receives). The count of forms measures neither the trusted base nor the proof effort: rows,
sampling laws, oracle kinds and commitment schemes have their own meanings and laws below the
language. Which elaborations are tested is stated in §11; what is proved of the core that they elaborate
into is stated in the core's specification (§9).

Why each form of §4.1 and §4.2 is syntax and not a library definition is the last column of §2.6.


---

## 5. Grammar

Notation: `[ x ]` is optional, `{ x }` is zero or more, `|` separates alternatives, quoted text is
a token. `Suite(X)` is `NEWLINE INDENT X { X } DEDENT`. `Name` is an identifier, `Role` is a
`Name` declared in a roster, `Number`, `String` and `ByteString` are the tokens of §3.2. Inside
`( )`, `[ ]`, `{ }` and static brackets a list may end with one more `,`. Each form has one
production. The grammar is one for all layers; §5.14 gives the layer of each production.

### 5.0 What a parser needs

The grammar is LL(1) after left factoring, with the decisions below. None needs a symbol table.

**GR1. Body: one expression, or statements.** A line of a suite of statements starts with one of
the words `mut`, `guard`, `if`, `match`, `for`, `return`, `open`, with `#`, with `Name :=`, with
`( ) NEWLINE`, or with anything else. In the last case the parser reads an `Expr` and looks at the
next token: `=`, `:`, `@` or `<-` make the line a statement whose left side is that expression
read again as a `Pattern`; `NEWLINE` makes it an expression. The expressions that can be read
again are a name, `_`, a tuple of such, and a record construction whose fields are names or
`f = pattern`; anything else is refused there. In a protocol body one more case: when the
expression is a call `Path CallArgs` and the next token is `NEWLINE`, or `@ (` followed by
`Name =`, the line is an `Application` without a binder. After `if Expr`, the token `:` makes a
statement and `then` an expression. A body of a `def` is one expression when its suite is one line
that is an expression; otherwise it is statements followed by `return`. No other expression is a
statement. **Messages:** "an expression is not a statement; bind it or return it"; "this is not a
pattern".

**GR2. `if` expressions.** An `if` expression stands only where an `Expr` is expected: as an
operand it is parenthesized, and so it is as the condition of a `guard`, whose `else` belongs to
the guard. **Message:** "parenthesize an `if` expression that is the condition of a guard".

**GR3. `:=` updates a name.** `xs[i] := e` and `r.f := e` have no production: a collection is
rebuilt by a comprehension or `++`, a record by `{r with f = e}`. **Message:** "`:=` updates a
`mut` name, not an element or a field; rebuild the value".

**GR4. A member definition against a function.** In the suite of a module, after `def Name (`:
when the next token is `)` and the one after it is `:` or `=`, or the next token is a `Name` and
the one after it is `,` or `)`, the item is a `MemberDef`; otherwise it is a `Def`. Three tokens
after `(` decide.

**GR5. Static terms.** A static argument, a side of a constraint and the subject of a `commit`
line are read by one production, `StaticTerm`: an expression in which the reserved type words are
also primaries and a tuple component may be named. The checker classifies the term by the sort of
the parameter it is bound to (SP3): a type (`[F; 4]` read as a collection type, `(A, B)` as a
tuple type), a natural, or a module. **Messages:** "`<A>` is a type; a natural is expected here";
"`<e>` is a natural; a type is expected here".

**GR6. Forms without a production.** A function type `fn(A) -> B` and a function literal
`fn(x) => e`; `distribution`; `affine struct`. `fn`, `distribution` and `affine` are not reserved:
they are names. **Messages:** "function types and function literals are not part of the language:
write a loop, a comprehension or a binder form"; "`distribution` is not part of the language:
sample or draw the bytes and apply the function"; "`affine` is not part of the language: a record
is `linear` or freely copied".

| Other decision | Tokens of lookahead |
|---|---|
| a named argument, a named static argument, a named field: `Name "="` | 2 |
| the label of a clause: `Name ":"` | 2 |
| a static name: `nat Name =`; a module member of an implementing module: `module Name =` not followed by `primitive` or `asset` | 4 |
| the suite of a module against its bound: after the name and the static parameters, `:` followed by `NEWLINE` opens the suite; any other token after `:` starts a `Bound` | 2 |
| a specification-only static parameter, and its value in a goal or among the static arguments of an application: `spec Name` | 2 |
| a `law` at the start of an item: the word `law` followed by a `Name` and `(` or `<` | 3 |
| `spec for` against `spec def`, `spec type` and `spec protocol`; `entry def`, `oracle def` | 2 |
| `_` as an inferred static argument: `_` followed by `,` or the closing bracket | 2 |
| the role map of an application: `@ (` after its arguments, then `Name =` | 4 |
| an attribute: `# [` then `site` or `kernel` | 3 |

### 5.1 Modules, imports, scopes

```ebnf
File         ::= "module" ModulePath [ StaticParams ] [ Where ] NEWLINE { Item }
ModulePath   ::= Name { "::" Name }
Item         ::= Use | Section | Module | Interface | TypeDecl | Struct | Enum | Def | OracleDef
               | Protocol | Relation | Contract | Scheme | Goal | Law | StaticName
Use          ::= [ "pub" ] "use" Path [ "as" Name | "::" "{" Name { "," Name } "}" ] NEWLINE
Section      ::= "section" ( StaticParams [ Where ] | Where ) ":" Suite(Item)
Module       ::= [ "pub" ] "module" Name [ StaticParams ] [ ":" Bound ] [ Where ]
                 ( ":" Suite(ModuleItem) | "=" ( Primitive | Asset ) )
ModuleItem   ::= Item | ModuleMember | MemberDef
Path         ::= Segment { "::" Segment }
Segment      ::= Name [ StaticArgs ]
```

### 5.2 Static parameters and arguments

```ebnf
StaticParams ::= "<" StaticParam { "," StaticParam } ">"
StaticParam  ::= [ "spec" ] Name [ ":" Bound ]
Bound        ::= Sort { "+" Sort }
Sort         ::= "nat" | "linear" | Path
Where        ::= "where" "(" Constraint { "," Constraint } ")"
Constraint   ::= StaticTerm ":" Bound
               | StaticTerm ( "<=" | "<" | "==" | "!=" | ">=" | ">" ) StaticTerm
StaticArgs   ::= "<" StaticArg { "," StaticArg } ">"
StaticArg    ::= [ Name "=" ] ( StaticTerm | "_" )
               | "spec" Name "=" StaticTerm
StaticTerm   ::= Sum
Size         ::= StaticTerm
StaticName   ::= [ "pub" ] "nat" Name "=" Size NEWLINE
```

In a `StaticTerm` the productions of `Primary` (§5.6) are extended by `"bool" | "nat" |
"rational" | "index" "<" Size ">" | "nonzero" "<" Type ">"`, and a component of a parenthesized
list may be `Name ":" StaticTerm` (GR5). `spec` stands only before a parameter whose bound is
`nat`; a specification argument, the second alternative of `StaticArg`, stands after the other
static arguments, in the static arguments of an application of a protocol (SP11). A `StaticName` stands in a file module, in a section and in a module; in a module
that implements an interface it also defines a natural member (TY2, SP8).

### 5.3 Types

```ebnf
Type         ::= "bool" | "nat" | "rational"
               | "index" "<" Size ">"
               | "nonzero" "<" Type ">"
               | "[" Type [ ";" Size ] "]"
               | "(" [ TupleField "," TupleField { "," TupleField } ] ")"
               | Path
TupleField   ::= [ Name ":" ] Type
```

### 5.4 Records, variants, type declarations

```ebnf
TypeDecl     ::= [ "pub" ] "type" Name [ StaticParams ] "=" ( Type NEWLINE | Primitive )
               | [ "pub" ] "spec" "type" Name [ StaticParams ] "=" External
Struct       ::= [ "pub" ] [ "linear" ] "struct" Name [ StaticParams ] ":" Suite(Field)
Field        ::= [ "pub" ] Name ":" Type NEWLINE
Enum         ::= [ "pub" ] "enum" Name [ StaticParams ] ":" Suite(Alternative)
Alternative  ::= Name [ "(" Type { "," Type } ")" ] NEWLINE
Primitive    ::= "primitive" "(" String { "," StaticArg } ")" NEWLINE
Asset        ::= "asset" "(" Name ")" NEWLINE
External     ::= "external" "(" String ")" NEWLINE
```

### 5.5 Functions

```ebnf
Def          ::= [ KernelAttr ] [ "pub" ] [ "spec" | "entry" ] "def" Name [ StaticParams ]
                 "(" [ Param { "," Param } ] ")" [ "->" Type ] [ Where ]
                 ( Body | "=" ( Primitive | External ) )
KernelAttr   ::= "#" "[" "kernel" "(" String ")" "]" NEWLINE
Param        ::= Name ":" Type
Body         ::= ":" Expr NEWLINE
               | ":" NEWLINE INDENT Expr NEWLINE DEDENT
               | ":" NEWLINE INDENT { Stmt } "return" Expr NEWLINE DEDENT
```

A `def` without `-> Type` returns `()`. `= External` stands only on a `spec def`. `KernelAttr`
stands only before a `Def` or a `MemberDef` that has a `Body` (FN5).

### 5.6 Expressions

```ebnf
Expr         ::= IfExpr | OrExpr
IfExpr       ::= "if" Expr "then" Expr "else" Expr
OrExpr       ::= AndExpr { "or" AndExpr }
AndExpr      ::= NotExpr { "and" NotExpr }
NotExpr      ::= "not" NotExpr | Compare
Compare      ::= Sum [ ( "==" | "!=" | "<" | "<=" | ">" | ">=" ) Sum ]
Sum          ::= Product { ( "+" | "-" | "++" ) Product }
Product      ::= Unary { ( "*" | "/" | "%" ) Unary }
Unary        ::= "-" Unary | Power
Power        ::= Postfix [ "^" Unary ]
Postfix      ::= Primary { "." Name [ [ StaticArgs ] CallArgs ] | "." Number
                         | "[" Expr "]" | "[" [ Expr ] ".." [ Expr ] "]" }
Primary      ::= Number | ByteString | "true" | "false"
               | Path [ CallArgs | "{" [ FieldInit { "," FieldInit } ] "}" ]
               | "(" ")"
               | "(" Expr ")"
               | "(" Expr "," Expr { "," Expr } ")"
               | "[" [ Expr { "," Expr } ] "]"
               | "[" Expr ";" Size "]"
               | "[" Expr "for" Pattern "in" Domain [ "if" Expr ] "]"
               | "{" Expr "with" Name "=" Expr { "," Name "=" Expr } "}"
               | ( "∑" | "∏" | "∀" | "∃" ) Pattern "∈" Domain "," Expr
               | "⟪" Expr "," Expr "⟫"
CallArgs     ::= "(" [ Argument { "," Argument } ] [ ";" Argument { "," Argument } ] ")"
Argument     ::= Expr | Name "=" Expr | "spec" Name "=" Expr
FieldInit    ::= Name [ "=" Expr ]
Domain       ::= Sum [ ".." Sum ]
```

### 5.7 Patterns

```ebnf
Pattern      ::= Name | "_"
               | "(" Pattern "," Pattern { "," Pattern } ")"
               | Path "{" FieldPattern { "," FieldPattern } "}"
FieldPattern ::= Name [ "=" Pattern ]
CasePattern  ::= Pattern | Number | "true" | "false"
               | Path [ "(" CasePattern { "," CasePattern } ")" ]
               | "(" CasePattern "," CasePattern { "," CasePattern } ")"
```

`Pattern` is irrefutable and stands in a binding, an event, a `for`, a comprehension and a binder
form. `CasePattern` stands only after `case`.

### 5.8 Statements

```ebnf
Stmt         ::= Binding | MutDecl | Update | EventStmt | Open | Guard | If | Match | For | Empty
Binding      ::= Pattern [ ":" Type ] [ "@" Holders ] "=" Expr NEWLINE
MutDecl      ::= "mut" Name [ ":" Type ] [ "@" Placement ] "=" Expr NEWLINE
Update       ::= Name ":=" Expr NEWLINE
Guard        ::= "guard" [ "@" Holders ] OrExpr [ "else" Reason ] NEWLINE
Reason       ::= "reject" | "abort" | "refused" | "exhausted"
If           ::= "if" Expr ":" Suite(Stmt) [ "else" ( ":" Suite(Stmt) | If ) ]
Match        ::= "match" Expr ":" NEWLINE INDENT Case { Case } DEDENT
Case         ::= "case" CasePattern ":" Suite(Stmt)
For          ::= "for" Pattern "in" Domain [ "collect" "(" Collected { "," Collected } ")" ]
                 ":" Suite(Stmt)
Collected    ::= Name "=" Expr
Empty        ::= "(" ")" NEWLINE
Holders      ::= Role | "(" Role { "," Role } ")"
Placement    ::= Holders [ "->" Holders ]
```

### 5.9 Protocols and events

```ebnf
Protocol     ::= [ "pub" ] [ "spec" ] ProtocolHead ":" NEWLINE
                 INDENT { Stmt } [ "return" Expr NEWLINE ] DEDENT
ProtocolHead ::= "protocol" Name [ StaticParams ] "roles" "(" Role { "," Role } ")"
                 "(" [ Port { "," Port } ] ")" [ "->" Results ] [ Where ]
Port         ::= Name ":" Type "@" Placement [ "private" ]
               | "spec" Name ":" Type
Results      ::= Result | "(" Result "," Result { "," Result } ")"
Result       ::= Name ":" Type "@" Placement

EventStmt    ::= [ SiteAttr ] ( Pattern [ ":" Type ] [ "@" Holders ] "<-" Event | Application )
                 NEWLINE
SiteAttr     ::= "#" "[" "site" "(" Name ")" "]" NEWLINE
Event        ::= Send | Draw | Sample | Query | Attempt | Application
Send         ::= "send" Expr [ "from" Role ] "to" Role { "," Role }
                 [ "as" "oracle" "<" StaticTerm ">" ]
Draw         ::= "draw" Type "from" Role "to" Role { "," Role }
Sample       ::= "sample" Type
Query        ::= "query" Expr [ "from" Role ] "at" Expr [ "deferred" ]
Attempt      ::= "attempt"
Application  ::= Path CallArgs [ "@" "(" Role "=" Role { "," Role "=" Role } ")" ]
Open         ::= [ SiteAttr ] "open" Claim { "," Claim } NEWLINE
Claim        ::= Sum [ "at" Sum "==" Sum ]
```

The body of a protocol has at least one line.

### 5.10 Oracles

```ebnf
OracleDef    ::= [ "pub" ] "oracle" "def" Name [ StaticParams ] "(" [ Param { "," Param } ] ")"
                 ":" Path [ Where ] ":" NEWLINE INDENT "at" Name ":" Expr NEWLINE DEDENT
```

A handle port is a `Port` whose `Placement` has `->`. An oracle send, a `query` and `open` are the
productions `Send`, `Query` and `Open` of §5.9. A kind, primitive or derived, is a `Module`
(§5.1).

### 5.11 Interfaces and implementations

```ebnf
Interface    ::= [ "pub" ] "interface" Name [ StaticParams ] [ Where ]
                 ( ":" Suite(Member) | NEWLINE )
Member       ::= "type" Name [ StaticParams ] [ ":" Bound ] NEWLINE
               | "nat" Name NEWLINE
               | "module" Name ":" Bound NEWLINE
               | [ "partial" | "spec" ] "def" Name [ StaticParams ]
                 "(" [ Param { "," Param } ] ")" [ "->" Type ] [ Where ] NEWLINE
               | ProtocolHead NEWLINE
               | Law
Law          ::= "law" Name [ StaticParams ] "(" [ Param { "," Param } ] ")" [ Where ] Body
ModuleMember ::= "module" Name "=" Path NEWLINE
MemberDef    ::= [ KernelAttr ] [ "spec" ] "def" Name "(" [ Name { "," Name } ] ")"
                 ( Body | "=" ( Primitive | External ) )
```

In a module that implements an interface, a type member is a `TypeDecl`, `Struct` or `Enum`, a
natural member a `StaticName`, a module member a `ModuleMember` or a `Module`, a function member a
`MemberDef`, and a protocol member a `Protocol` whose head repeats the member's. A `Law` stands as
a member of an interface and as an item of a module or of a section (SP10). The body of a `law`
is one expression. An interface without members is written without a suite. `= External` stands
only on a `spec def` member.

### 5.12 Specification items

```ebnf
Relation     ::= [ "pub" ] "relation" Name [ StaticParams ]
                 "(" [ Param { "," Param } ] [ ";" Param { "," Param } ] ")" [ Where ]
                 ( Body | "=" External )
Contract     ::= "spec" "for" Path ":" Suite(Clause)
Clause       ::= "requires" [ Label ] Expr NEWLINE
               | "ensures" [ Label ] Expr NEWLINE
               | "invariant" [ Label ] Expr "at" Name NEWLINE
               | "reduces" [ "@" Role ] [ Label ] Expr "to" Expr NEWLINE
               | "proves" [ "@" Role ] [ Label ] Expr NEWLINE
               | "through" Expr "at" Name NEWLINE
               | "knowledge" [ Label ] Expr "by" Extractor [ "or" Expr [ "by" Path ] ] NEWLINE
               | "zero_knowledge" [ Label ] "by" Extractor
                 [ "using" Ability { "," Ability } ] NEWLINE
               | "charge" SiteRef "<=" Expr NEWLINE
Extractor    ::= Path | "external" "(" String ")"
Label        ::= Name ":"
Ability      ::= "coins" | "programming" | "trapdoor"
SiteRef      ::= "sites" "." Name { "." Name }
```

A `spec def` is the production `Def`; a `spec type` the second alternative of `TypeDecl`; a
`spec protocol` the production `Protocol`; a specification port the second alternative of `Port`;
a specification argument the third alternative of `Argument`; a specification-only static
parameter the production `StaticParam` with `spec`; a law the production `Law`. The body of a
relation is one expression. In a `zero_knowledge` clause `using` never follows `external( … )`;
after a `Path` it lists the abilities that the simulator is given, and it is left out when there
are none (SX6).

### 5.13 Schemes, goals, entries

```ebnf
Scheme       ::= [ "pub" ] "scheme" Name "=" Path ":" Suite(SchemeLine)
SchemeLine   ::= "construction" ( "derived" "(" Path ")" | "interactive" | "authored" ) NEWLINE
               | "prover" Role NEWLINE
               | "offline" Role { "," Role } NEWLINE
               | "ideal" Role { "," Role } NEWLINE
               | "context" Name ":" Type NEWLINE
               | "commit" ( StaticTerm | SiteRef ) "with" Path [ "(" Key { "," Key } ")" ] NEWLINE
               | "pin" SiteRef "=" Path ":" ByteString NEWLINE
               | "grind" Size "bits" "at" SiteRef { "," SiteRef } NEWLINE
               | "retry" Size "from" SiteRef NEWLINE
               | "samples" "derived" "by" Path NEWLINE
               | "layout" Path ( NEWLINE | ":" Suite(Adjust) )
Key          ::= ( "prover_key" | "verifier_key" ) "=" SiteRef
Adjust       ::= "carry" SiteRef NEWLINE
               | "recover" SiteRef "by" Path NEWLINE
Goal         ::= [ "pub" ] "goal" Name "=" Path "(" Path { "," GoalArg } ")"
                 [ "<=" Expr ] NEWLINE
GoalArg      ::= Name "=" GoalValue
               | "spec" Name "=" Size
GoalValue    ::= Path [ CallArgs ]
               | "(" GoalValue "," GoalValue { "," GoalValue } ")"
```

An entry is the production `Def` with `entry`.

### 5.14 The layer of each production

| Layer | Productions |
|---|---|
| B | `Relation`, `Contract`, `Clause`, `Extractor`, `Label`, `Ability`, `Goal`, `GoalArg`, `GoalValue` |
| C | `Scheme`, `SchemeLine` without its `commit` alternative, `Key`, `Adjust`, `SiteRef` in a line of a scheme; `Def` with `entry` |
| D | `OracleDef`, `Query`, `Open`, `Claim`; in `Send`, the tail `"as" "oracle" "<" StaticTerm ">"`; `Placement` with `->`; the `commit` alternative of `SchemeLine` |
| A | every other production, among them `Law`, `StaticName`, `Def` with `spec`, the specification port of `Port` and the specification argument of `Argument` |


---

## 6. Static semantics

### 6.1 Names

**NL1. Declarations.** The declarations of a module are visible in the whole module, in any
order. No instance refers to itself, directly or through others: the test is made on instances
(SP7), after the expansions of §7.6, so that it covers references through module arguments and
through the `Send` and `Open` of derived kinds. **Message:** "`<f>` refers to itself through
`<g> → <h>`; a definition cannot be recursive".

**NL2. One binding per name.** A local name (a parameter, a port, a binder, a loop index, a
collected name) is bound once in a definition: a suite does not rebind a name of an enclosing
suite, and no local name has the name of a static parameter in scope. Two suites of which
neither encloses the other (the arms of a choice, two loops one after the other) may each bind
one and the same name: only a name of an enclosing suite is not bound again. A local name may
have the
name of a declaration or an import of the module; it then hides it in that definition. Two
declarations of a module, or a declaration and an import, do not share a name.
**Messages:** "`<x>` is already bound at line <n>; a local name is bound once"; "`<n>` is a
static parameter here and occurs in types; a binder does not shadow it".

**NL3. Four ways to find a name.** (a) `use`: `use a::b` binds `b`; `use a::b as c` binds `c`;
`use a::b::{X, y}` binds `X` and `y` and not `b`. `pub use` exports what it binds; a name bound
by a `use` without `pub` is not reached from another module, and a path that goes through it is
refused by this rule. A `use` inside
a `section` may mention the section's static parameters. Every `use` names something, whether the
module uses the name or not. The path of a `use` is an absolute module path: its longest prefix
that names a module is the module, and what follows names a declaration of it. Every other path
starts with a name in scope: a local name, a static parameter, a declaration or an import of the
module, or a name of the prelude (NL4). (b) `::` through a module, an implementing module or
a static
parameter with an interface bound (`C::Value`, `fri::LowDegree`), and through a type of a sort,
for the members of its sorts: a type (`G::Scalar`), a natural (`F::Order`), a function
(`G::generator()`, `F::from_nat(n)`, `F::to_nat(x)`). (c) `::` through a protocol, a scheme or a layout module,
for its generated members only (§8). (d) `.` through the home module of a value's type (NL5). An
alternative of a variant is `Enum::Name`, or the bare name where the type expected is that
variant. **Messages:** "`<x>` is not bound: it is no local name, static parameter, declaration or
import of this module"; "module `<zkc::algebra>` has no `<cardinality>`".

**NL4. Files and the prelude.** The header of a file is the only statement of its module path;
no two files have one path. In scope everywhere, without `use`, are the names of the module
`zkc::prelude`: `byte` (the alias of `index<256>`), `length`, the sorts `Group`, `Ring`,
`PrimeOrderGroup`, `Field`, `PrimeField`, `ExtensionField`, `TwoAdicField`, and `Oracle`,
`Pending`, `data`; and the functions `sum`, `product`, `all`, `any`, `inner` of §3.5, which have
no declaration. `log2` is an operator of sizes (TY2). Nothing else is in scope without `use`:
`Option` is imported from `zkc::option`, a kind from the module that declares it. A local name may
hide a name of the prelude; a declaration of a module outside the core library may not have one
(NL10).

**NL5. Dot call.** `e.m<σ>(a…)` with `e: T<…>` and `T` declared in module `H` is `H::m<σ>(e, a…)`
when `m` is a function of `H`. On a value of an opaque type member `X::T` it is `X::m<σ>(e, a…)`,
a member of the interface of `X`, resolved in the opaque typing (SP12). It applies to functions
only. A field named `m` takes precedence when no argument list follows. **Message:** "`<T>` has
no function `<m>` in its home module `<H>`".

**NL6. Operators.** The meaning of an operator or a mathematical form is given by §3.5. On a
reserved type and on a type of a sort it is a row of §7.4, selected by the sort of the left
operand. On a type `T` declared in module `H` it is the function of the fixed name in `H`; a type
without that function does not have the operator, and a type has `∑` when it has `add` and
`zero()`, `∏` when it has `mul` and `one()`. The function `at` cannot stop. A module cannot give
an operator to a reserved type or to a type of a sort.

*Operators on a type member.* No type carries a spelling. At an instance a type member `M::T`
is its definition (SP8, TY3), and an operator on a value of it is what this rule gives the
definition: a row for a type of a sort, a function of the home module for a declared type. In a
definition generic over a module parameter `X: I` the type member `X::T` is opaque (SP12), and
the opaque typing is where an operator, a mathematical form and a dot call on a value of `X::T`
are resolved: each to the member of the fixed name that `I` declares, or that an interface
declares which the `where` of `I` requires of `Self`. An interface that wants its type member to
have operators declares them (`add`, `sub`, `mul`); an operator whose member `I` does not
declare is refused, whatever the instance is. The instance typing uses that resolution: at each
instance the operator is the call of that member of the module that `X` stands for. A definition
generic over `X: I` therefore has one meaning that does not depend on the instance. A number
does not check against an opaque type member (TY6); an interface that wants constants declares a
function for them.

**Messages:** "`<T>` has no function `<add>` in its home module `<H>`"; "`<op>` is not defined for
`<T>` and `<U>`"; "`⟪a, b⟫` takes the points first and their scalars second: write
`⟪<g>, <a>⟫`"; "`notation` is removed: an operator means the function of its fixed name in the
home module of the type"; "`<Algebra>` declares no `<mul>`: an operator on its type member
`<X::T>` is a member of the interface".

**NL7. Visibility.** A declaration or a field without `pub` is visible in its module only; so is
an import without `pub`, which NL3 refuses when it is reached from outside. A
record with a field that is not `pub` is constructed, and matched by a record pattern, only in
its module. **Message:** "`<T>` has a field that is not `pub`; it is built only in `<H>`".

**NL8. Case.** By convention a type, an interface, an implementing module, a protocol, a
relation, a scheme and a role start with a capital letter; a namespace module, a function, a
field and a value do not. The grammar does not depend on case.

**NL9. Bindings to what is outside the language.** A row is executable; the formal library is not.

| Form | Binds |
|---|---|
| `type T<…> = primitive("row", args)` | a type of the vocabulary: a field, a group, a sealed type. Its sorts and the values of their members are those the vocabulary gives the row |
| `def f<…>(…) -> T = primitive("row")`; in an implementing module, `def f(x…) = primitive("row")` | a function to a row. A row cannot stop |
| `module M<…>: I = primitive("row", args)` | a module of the vocabulary that implements `I`: a hash, a pairing, a suite of the catalogue. Its type and natural members are those the vocabulary gives the row |
| `module M: I = asset(name)` | a module whose members are read from an asset of the project manifest. `I` is an interface whose members are naturals and functions without parameters that return data: it has no type member, no function with a parameter and no law. A natural member is the asset's number of that name; a function member returns the asset's content of that name, decoded at the type of the member. Decoding is an admission check of the build: an asset whose content does not decode at the type refuses the build, with the member and the position. The digest of the asset in the manifest is a static argument of the module, and so in the deployment identity of every scheme that reaches it |
| `spec type T<…> = external("name")` | a type that exists only in the formal library |
| `relation R(…) = external("name")`, `spec def f(…) = external("name")`; in an implementing module, `spec def f(x…) = external("name")` | a predicate or a function of the formal library; the source checks only the header |
| `#[kernel("name")]` before a `def` with a body | an implementation of that definition (FN5); the body stays its meaning |

The signature written is checked against the row of the printed vocabulary at each instance; what
a row costs and on which domain it is total are read from the vocabulary and are not written. A
type of the vocabulary is identified by its row and its static arguments: two declarations that
bind one row at the same arguments declare one type. A
type is not bound to an asset, and neither is a relation: the relation that imported data denotes
is a formula in source over the module that reads the data (§E). A deployed `def` is not bound to
`external`, and a `spec def` is bound to a row only for the projections of a sealed type
(`zkc::oracle::position`). A row that the vocabulary does not have is refused in a library under
`zkc::`; a row of a project or of a library not yet ported is reported, and its signature is
taken as written. The manifest of assets, and how the digest of an asset becomes a static
argument, are settled with layer E, which uses them. A row of a project that is total only on a
domain is bound by a
declaration that is not `pub`, and a `pub` function that guards and then applies it is what other
modules call.
**Messages:** "`<oracle.contents>` is not a row of the vocabulary"; "a type is not bound to an
asset; bind a module: `module M: I = asset(name)`"; "a relation is not bound to an asset: write
its formula over the module that reads the data"; "`<M>` is bound to an asset, and its interface
`<I>` has the type member `<T>`: an asset gives naturals and data"; "`external` names the formal
library; only a `spec def` or a `relation` is bound to it"; "`external` names the formal library;
a type of the formal library is a `spec type`".

### 6.2 Static parameters, bounds, instantiation

**SP1. Scopes.** A file module, a nested module, a `section` and a single declaration are the
scopes that carry static parameters and a `where`. Every parameter and every constraint of a
scope belongs to every member, in order, outermost first. A `section` has parameters, a `where`,
or both. A static name `nat N = e` of a file module, a section or a module belongs to its scope
as a member does: it is evaluated with the scope's parameters (TY2). A conjunct of a `where`
that mentions a specification-only static parameter belongs to the specification items of the
scope only (SP11). A `scheme`, a `goal` and an
`entry def` have no static parameters: they close what they name.

*Where to declare a parameter.* On the smallest scope all of whose members use it at one value:
the field or the group of a library on its file module or on a section; the size of one protocol
on that protocol. A parameter that one member uses at several values is declared on the
declaration: a relation that a `through` clause applies at every boundary of a loop that halves
its state (`InnerProductRelation<n>`, used at `n`, `n - 1`, …) has `n` of its own, and a helper
whose result is half its argument writes its signature so that inference solves it,
`[T; 2^(m + 1)]` in and `[T; 2^m]` out (SP6 step 4).

**SP2. Inside and outside.** Inside a scope a member is named bare and stands for itself at the
scope's parameters; static arguments after it give its own parameters only. From outside, the
scope's parameters come first: `m<A…, B…>`; for a named scope also `S<A…>::m<B…>`, and
`use S<A…>::{m}` or `use S<A…> as T` fixes `A…` once. A `section` has no name and is reached
only by the first form.

**SP3. Static things.** A static parameter is a type, a natural or a module. Its bound says
which: no bound (a type of freely copied data), `linear` (a type of any use mark), a sort (a
type), `nat` (a natural), an interface that is not a sort (a module that implements it). `A + B`
requires both. A parameter written with `spec` is a natural that only the specification reads
(SP11).

A *sort* is the interface `zkc::algebra::Group`, or an interface whose `where` requires
`Self: S` for a sort `S`. Only the vocabulary implements a sort: `T: S` holds exactly when the
vocabulary gives the type `T` the sort `S`, with a value for every type and natural member of `S`
and a row for every function member. The sorts are a closed table (§2.5); `CORE-LIBRARY.md` gives
their members. They form one hierarchy:

- a `Group` is an abelian group written additively, with a right action of its `Scalar`, a
  `Ring`: `x * 1 == x`, `x * (a * b) == (x * a) * b`, `(x + y) * a == x * a + y * a` and
  `x * (a + b) == x * a + x * b`;
- a `Ring` is a `Group` that is its own `Scalar`, with a multiplication that is commutative and
  has the unit `1`. What is a ring's is declared by `Ring`: the unit, number literals,
  `from_nat`, `Characteristic`, `^` by a natural, and `∏`;
- a `Field` is a `Ring` in which every `nonzero` has an inverse: it adds division by a `nonzero`,
  and `nonzero<F>` is a type for a field `F` only;
- finiteness is stated where `Order` is: a type of sort `Group` has `Order` elements;
- a sized collection of elements of a `Group` is a `Group` with the scalar of its elements, so a
  vector over a ring has `+`, `-`, `* scalar` and `⟪ ⟫` (TY11); it is not itself a `Ring`. Its
  `Order` is the `Order` of its elements to the power of its size.

These are the laws of the sorts. They are stated here and not written as `law` members: the
vocabulary gives each type a model in the formal library that is an instance of the structure
with these laws (SP10). A module that interprets a signature without satisfying them, such as a
degree interpretation of an algebra (§E), is not of a sort. Every sort is known to the compiler
(NL10), and for each sort the vocabulary states a default representative, a type of that sort
(SP7). A bound is checked on instances: that the body of a definition generic over `G: Group`
uses a scalar only as a ring is seen at an instance whose scalar is not a field, which is the
known lateness of typing on instances. In a sort, `Self` is the type, and a member is reached as
`T::m`.
**Messages:** "`<T>` is not of sort `<Field>`, which `<F>` of `<m>` requires"; "`<M>` does not
implement `<I>`, which `<R>` of `<m>` requires"; "`<G>` has no member `<identity>`; its sorts are
Group, PrimeOrderGroup".

**SP4. Constraints.** A `where` holds: a bound on a static path (`C::Value: TwoAdicField`,
`Self: Kind`); a comparison of sizes (`<=`, `<`, `==`, `!=`, `>=`, `>`); an equality of types.
The constraints of a `where` are its conjuncts. Every term is static: a constraint never mentions
a port, a parameter or a `spec` port, and it contains no call of a function. A `where` that calls a function is refused where it stands, at
the declaration and before any instance; a member of a static thing (`F::Order`) and the size
operator `log2( )` are not calls. A conjunct that mentions a specification-only static parameter
is a specification conjunct: it constrains specification items and goals, and is no part of the
admission of a deployed item (SP11). The `where` of an interface may mention its members and
`Self`; it is then a condition on every implementing module. A constraint `Self: I` requires
every implementing module to implement `I` and puts the members of `I` in scope in the interface.
For a module without a body (bound to the vocabulary or to an asset, or the kind of an
`oracle def`), an equality `Member == T` defines the member. A constraint is evaluated at each
instantiation (SP7); nothing is derived symbolically. A `where` may also follow the signature of
a function member of an interface, where it is a condition of each application of that member;
the head of a `law`, where it is a condition of the instances at which the law is typed and is
an obligation (SP10); and the head of a `relation`, where it is a condition of each application
of the relation (SX3). **Messages:** "`<m>` requires `<constraint>`, which is `<20 <= 18>` here
and does not hold"; "the `where` of `<f>` calls `<bound>`: a constraint is over static terms, and
a call is not one".

**SP5. Arguments.** A static argument list is positional or named; positional arguments precede
named ones. A list in which two or more natural arguments are numerals writes its naturals by
name (`Gkr<d = 4, w = 2>`); naturals given by names or terms may be positional
(`Circuit<d, w>`). A positional list may be shorter than the parameter list: the missing
trailing arguments are inferred; `_` stands for an inferred argument that is not trailing. A
named list omits what is inferred. **Message:** "`<m>` takes the naturals `<d>`, `<w>`: write
them by name, `<m><d = …, w = …>`".

**SP6. Inference.** The static arguments that a reference does not write are found by this
procedure, at the instance in which the reference stands (so every type of an argument is closed
and every size in it is a number).

1. *Unknowns.* The parameters of the callee that are not written and are not fixed by the scope
   the reference is inside (SP2). A specification-only parameter is never an unknown: no step
   solves it and no step reads it (SP11).
2. *Equations from the arguments, left to right.* For each value argument, in the order of the
   parameters, the parameter's type is matched against the type of the argument. A `spec` port
   and its argument are skipped. An argument that needs an expected type gives no equation: a
   number, a power of a number. A sequence literal of such elements gives its length only.
3. *Matching a type.* A parameter type that is an unknown type parameter is solved by the type of
   the argument. An alias is replaced by its definition, with its parameters standing for the
   written terms. `nonzero<T>` against `nonzero<U>` or against `U` matches `T` against `U`. Two
   applications of one record, variant, sealed type, `Oracle` or `Pending` are matched argument
   by argument: a type argument by this step, a natural argument by step 4, a module argument by
   step 3a. `[T; s]` against `[U; n]` matches `T` against `U` and gives the equation `s = n`;
   `index<s>` against `index<n>` gives `s = n`. Anything else gives no equation.

   3a. *Matching a module.* A module term that is one unknown name is solved by the module. Two
   applications of one module (`table<T, 2^k>` against `table<Fr, 1024>`) are matched argument
   by argument, by steps 3, 3a and 4.
4. *Solving `s = n`* (`s` a size term of the callee, `n` a number). When `s` has no unknown, the
   equation is left to typing. When `s` is one unknown name, it is solved. When `s` is `a + b` or
   `a - b` and one side has no unknown, the other side is solved against the difference or the
   sum. When `s` is `a ^ b`, `a` has no unknown and is at least 2, and `n` is a power of `a`,
   `b` is solved against the exponent, which is then the only one. With `a` equal to 0 or 1 the
   equation is set aside: `1^n = 1` determines no `n`. Every other equation (a product, two
   unknowns in one sum) is *set aside*.
5. *Retry.* After each solution the equations set aside are tried again, in the order they were
   set aside, until a pass solves nothing.
6. *The result.* If unknowns remain and the call has an expected type, the result type is matched
   against it (steps 3 to 5).
7. *Check.* Every unknown has a value, or the reference is refused. A value found twice must
   agree; a disagreement shows as a type error at the argument. A type found twice agrees when
   one of the two widens to the other (TY5), and the parameter takes their join: `F` and
   `nonzero<F>` give `F`.

Nothing is searched and no step depends on the order in which equations of one argument arise.
The same procedure finds the static arguments that a `commit` line leaves to the kind (SC5).
**Messages:** "cannot infer `<N>` of `<m>`; write `<m><N = …>`"; "`<n>` of `<m>` occurs only in
the specification port `<p>`; write `<m><n = …>`".

**SP7. Instantiation.** Typing is defined on instances. An *instance* is a declaration with a
closed value for each of its static parameters: a closed type, a number, a module at its own
arguments. The roots are every `scheme`, `goal` and `entry def`; the protocol instance that a
`scheme` names; and every declaration that has no static parameter other than specification-only
ones (SP11), neither of its own nor of a scope around it, which is its own single instance. A
module without static parameters is such a root. A member of an interface is not a root: it is
typed in the implementing modules (item 7). A reference `m<σ>` reached from an instance
gives the instance of `m` at the values of `σ`; an instance is checked once and remembered by
its declaration and values.

At an instantiation the checker does, in this order, and stops at the first failure:

1. binds the written static arguments, by position and by name (SP5), each evaluated in the
   instance that writes it and classified by the sort of its parameter (GR5);
2. infers the others (SP6);
3. checks the bound of every parameter (SP3), outermost scope first;
4. evaluates every `where` constraint, in the order written, outermost scope first (SP4);
5. evaluates the types of the signature: every size is evaluated (TY2);
6. checks the arguments of the reference against the parameter types;
7. checks the body, statement by statement; a reference in it is instantiated when it is reached,
   depth first. An arm of an `if` that a static condition does not take is not checked, and a
   reference in it is not reached (TY9). For an instance of an implementing module: every
   function member, whether or not anything calls it, at the default values of the member's own
   static parameters, and every law of its interfaces at which the `where` of the law holds; for
   every module, each `law` of its own (SP10);
8. for a definition generic over a module parameter, the check of item 7 is the second of two
   typings of the body: the first types it with the type members of that parameter opaque.
   SP12 states both typings and their order.

A failure names the instantiation chain, innermost first. **Message form:**

```text
[TY7] line 22: `j + 2 ^ k + 1` can be as large as 1048576; `source` has 1048576 elements
      in fold<k = 19> (fri.zkc:66)
      in LowDegree<F = KoalaBear4, W = table<KoalaBear4, 1048576>, LogSize = 20, …> (fri_example.zkc:11)
      in scheme FriTest (fri_example.zkc:11)
```

*What no root reaches.* Names are resolved in every declaration, reached or not: an unbound name
is an error wherever it stands. A **public** declaration with static parameters that no root of
its package reaches is checked at its *default instances*. The package is the set of files that
the tool is given: a module of a library that those files reach by a path is not of the package
and gets no default instances; given to the tool itself, it is its own package. The default
instances are:

- each natural parameter at 0, 1, 2 and 3 and, when a `where` of its scopes bounds it above by
  a term without natural parameters (`k <= F::TwoAdicity`, `n < 64`), also at the largest value
  that this bound admits, the term evaluated at the types and modules of the default instance:
  every combination for up to three naturals; beyond that, the four instances with all naturals
  equal at 0, 1, 2 and 3, and each natural at each of its other values with the others at 1;
- each type parameter at one type: `bool` when it has no sort; otherwise the default
  representative that the vocabulary states for the sort of its bound, so that no tie arises.
  For a bound of several sorts it is the representative of the first sort written whose
  representative has all of them; when none has, the declaration has no default instance;
- each module parameter at the first module of the program, the package's own files first, that
  implements its bound, with that module's static arguments solved against the bound (SP6) and
  its others at their defaults.

A default instance whose `where` does not hold is skipped; a law whose own `where` does not hold
at a default instance is skipped there (SP10). A specification-only static parameter takes the
values 0, 1, 2 and 3 where a specification item is typed at a default instance (SP11). A
zero-iteration instance is a case like any other: a definition that reads `xs[0]` of a `[T; n]` states `where (1 <= n)`. The tool
reports, for each such declaration, how many instances it checked and the first of them; a
declaration that is not public, or for which no default instance exists, is resolved for names
only, and the tool says so. Default instances are a convenience for the author of a
library: every instance that a program uses is checked when it is instantiated, so what the
default instances miss costs a late message and never soundness.
**Messages:** as at any instance, with the chain line "in default instance `<first<T = bool,
n = 0>>`".

**SP8. Interfaces.** A module `M<A>: I<B>` defines every member of `I` and no member that `I`
lacks; it may hold other declarations, which are its own. A type member is defined by a type
with the member's parameters, and satisfies the member's bound; a natural member by a static name
(`nat Degree = 1`); a module member by a module that implements the member's bound; a function
member by its binders and a body, a row or, for a `spec def`, an external name (`def f(x…): e`,
`def f(x…) = primitive("row")`); a protocol member by a protocol whose head equals the member's.
A member of an implementing module is written `spec` exactly when the member of the interface is:
a member that the interface declares `def` is deployed code, defined by a body or a row, and is
never a `spec def` and never bound to `external`. The signature of a function member is the
interface's, read with the interface's static arguments and with each member name standing for
`M`'s definition; the member's own static parameters are in scope in its body under the names the
interface gives them. `Self` in an interface is the implementing module (in a sort, the type). A
member's own name is not in scope in its definition. `M<A>::T` is its definition to every reader. An interface is satisfied only by a module that names it: a module
that implements `Rows<T, n>`, whose `where` requires `Self: Kind`, names both. **Messages:**
"`<M>` does not define `<member>` of `<I>`"; "`<M>` defines `<member>`, which `<I>` does not
have"; "`<I>` declares `<write_natural>` as a `def`: `<M>` defines it as deployed code, not as a
`spec def`"; "`<I>` declares `<table>` as a `spec def`: write `spec def <table>(…)`".

**SP9. `partial`.** A function member written `partial def` may be implemented by a function that
can stop; one written `def` may not. **Message:** "`<M>::<f>` can stop; `<I>` declares `<f>`
without `partial`".

**SP10. Laws.** A `law` is a `bool` specification expression that cannot stop. As a member of an
interface it is over the members of the interface: it is an obligation of each implementing
instance and an assumption of each proof about a consumer. As an item of a module or of a section
it is over the definitions of that module: it states a proposition about them and leaves one
obligation record of the module, per instance of its scope. A law is typed at every instance that
the checker reaches, the default ones included (SP7): for a law of an interface the instances of
the implementing modules, one instance of the law per instance of an implementing module; for a
law of a module the instances of its scope. That it holds for all
values of its parameters is a statement of the formal library.

*A `where` on a law.* A law may carry a `where` over its own static parameters, the members of
the interface and the static parameters in scope (SP4). The law is typed, and is an obligation,
only at the instances at which its `where` holds.

*A closed law is decided by evaluation.* A law is *closed* when it has no parameter and no static
parameter of its own. A closed law of a module that is bound to the vocabulary is a statement
about the model of the vocabulary and is never evaluated. A closed law of a module in source is
evaluated at each implementing instance that a root reaches (SP7), by the executor of the model
of the formal library, which runs the bodies of the functions that the expression applies. A
kernel is never substituted for a body when a law is decided. The evaluation has a budget of
steps actually taken, which the configuration of the build gives; this reference fixes none, and
no cost is computed in advance to decide whether to start. The outcome is one of three:

- *decided true*: the obligation is discharged by computation;
- *found false*: an error of the build, by policy (SX10);
- *not decided*: the budget ran out, or the expression applies a function bound to `external`.
  The law stays an obligation like any other and is never reported as holding. Running out of
  budget is an incomplete check: it refuses nothing and proves nothing.

Default instances type a closed law and do not evaluate it.

A law, its proof or its absence never selects an executable body or an optimization, and never
changes whether a program is admitted for execution: a module with an unproved law compiles and
runs, and the goals that rest on the law stay open (SX10). The laws of a sort are not written as
`law` members: SP3 states them, and the vocabulary gives each type a model in the formal library
that is an instance of the corresponding structure there. **Messages:** "the law `<degree>` of
`<Air>` is false at `<Fibonacci>`"; "the law `<degree>` of `<Air>` at `<Fibonacci>` was not
decided within the budget of <n> steps: it stays an obligation"; "the law `<agree>` can stop; a
law is an expression that cannot stop".

**SP11. Specification-only static parameters.** A static parameter written `spec n: nat` is a
natural that only the specification reads: the tolerated number of errors of a proximity
statement is one.

1. *Where it is declared.* In any static parameter list, after the parameters that are not
   `spec`. Its bound is `nat`.
2. *Where it occurs.* In specification items: in a clause of a `spec for`, in a `relation`, a
   `spec def`, a `spec type` and a `law`, in the type of a `spec` port and in a `spec` argument;
   in a specification argument of an application (item 4); and in a `where`. It is refused in
   every deployed type and in every size and every other static argument of deployed code.
3. *Specification conjuncts.* A conjunct of a `where` that mentions a specification-only
   parameter is a *specification conjunct*. It constrains the specification items of its scope
   and the goals. It is checked where a value is given: at a goal and at an application. It is
   no part of the admission of a deployed item, whose instance exists whether or not the
   conjunct holds.
4. *Who gives it its value.* A scheme does not close it (SC1). A goal gives a value to every
   specification-only parameter of the protocol instance of its scheme, `spec n = e`, with `e` a
   static term without free names (GL2). An application of a protocol that has
   specification-only parameters gives each of them as a specification argument, after the
   other static arguments: `C<…, spec n = term>(…)`, with `term` a static term over the static
   naturals in scope and the caller's own specification-only parameters. Every application
   gives every specification-only parameter of its callee, as it binds every `spec` port (SX4),
   except those of a scope that the caller shares with the callee, which are the caller's own;
   a goal or an application that leaves one out is refused. Inside the scope that declares it, a
   specification item reads the parameter as a static natural under its name. A reference from
   a specification item to a specification item of another scope writes it as it writes any
   static argument (SP5).
5. *What it is not part of.* It is in no instance of a deployed declaration (SP7) and in no
   identity (§7.1): two values of it give the same role programs and the same proof bytes, and a
   specification argument is erased with the other specification material (SX2). Inference
   neither solves it nor reads it (SP6).
6. *Instances of specification items.* A specification item that reads a specification-only
   parameter is instantiated per goal, with the values that the goal gives and, for a callee,
   the values that the applications compute from them. Without a goal it is typed at the default
   values 0, 1, 2 and 3 (SP7).

**Messages:** "`<e>` is a specification-only static parameter; it does not occur in the type of
the port `<p>`"; "`spec` marks a natural: write `spec <e>: nat`"; "the specification-only
parameters stand last: write `<k: nat, spec e: nat>`"; "the goal `<sound>` gives no value to the
specification-only parameter `<e>` of `<SpotCheck>`: write `spec <e> = …`"; "`<SpotCheck>` has the
specification-only parameter `<e>`: write `<SpotCheck><…, spec e = …>(…)`"; "the goal `<sound>`
gives `<e> = 9`, and `<SpotCheck>` requires `<e <= n>`, which is `9 <= 8` here".

**SP12. A type member of a module parameter is opaque.** A definition generic over a module
parameter `X: I` is typed twice at every instance, and it is accepted only when both typings
succeed.

*The opaque typing* comes first. Each type member `X::T` of `X` that no `where` in scope equates
with a type is a fresh type, one per member and per static arguments of the member. The fresh
type is equal to no other type; two applications of one member are matched argument by argument
(SP6) and are equal when their arguments are. Naturals, sizes and every other static argument
are those of the instance, so typing stays on instances (SP7). The fresh type has only what `I`
declares for it:

1. the sorts of the bound that `I` writes on the member (`type Target: Group`), with their
   operators and their members; and its use mark, freely copied unless that bound is `linear`;
2. the members of `I`, and of the interfaces that the `where` of `I` requires of `Self`, in
   whose signatures the member occurs;
3. the operators, the mathematical forms and the dot calls that are members of `I` by NL6
   (`add`, `sub`, `mul`, `equal`, `zero`, …).

Every other operation of the general tables is absent on it: `==` and `!=` (TY12) unless `I`
declares `equal`, the order, `match`, literals, and the operators and forms whose function `I`
does not declare. An operator that is absent on it is absent on every tuple, record, variant
and collection that contains it (TY12). What does not observe a value stays: it may be bound,
passed, returned, sent,
placed in a tuple, a record or a collection, and taken out again by position. The opaque typing
resolves every operator, mathematical form and dot call on a value of the fresh type to a member
of `I` (NL6).

*The instance typing* follows. In it `X::T` is its definition, and each operator that the opaque
typing resolved is the call of that member of the module that `X` stands for. No type carries a
spelling between the two typings: what the instance typing takes from the opaque one is the
resolution of those operators, by their place in the text.

A callee that the definition instantiates with the fresh type, as a type argument or through a
module argument, is typed at it: a helper generic over a type parameter that compares its
arguments is refused at that instance, so a helper cannot observe the carrier either. A `where`
in scope that equates the member with a type (`X::T == F`) makes it that type in both typings:
the definition has asked for the carrier.

A definition that passes uses its carrier only through the interface. The formal library has one
theorem for all such definitions, over the local dialect: two interpretations of `I` that are
related by a relation which the members preserve give related results. With homomorphisms as the
relation, every evaluation of a constraint function agrees with its polynomial meaning; with the
relation "the degree of the polynomial is at most the degree value", a degree interpretation is
a sound upper bound (§E). The rule applies to a `def`, a `spec def`, a `relation`, a `protocol`
and a member definition whose static parameters, or those of its scope, include a module
parameter; it does not apply inside a module to the module's own type members, which are their
definitions there. **Messages:** "`==` is not defined for `<X::T>` in a definition generic over
`<X>: <Algebra>`: `<Algebra>` declares no `equal` for its type member"; "`<F>` is not `<X::T>`:
in a definition generic over `<X>` the type member is opaque; apply `<X::constant>`", each with
the chain line "in the opaque typing of `<indicator>` over `<X>: <Algebra>`".

### 6.3 Types, sizes and facts

**TY1. Types.** The reserved types: `bool`; `nat` (a natural number, of any size); `index<s>` (a
natural below `s`); `nonzero<F>` for a field `F`; `[T; s]` (exactly `s` elements); `[T]` (a
collection whose length is a run-time value); tuples, whose components may be named in the type;
`rational`, in specification expressions only (charges, ceilings, budgets, bounds). Besides them:
a type of the vocabulary (a field, a group, a sealed type such as `Oracle<K>` and `Pending<K>`);
records; variants; aliases (`byte` is `index<256>`); a `spec type`, in specification items only.
There is no type of functions. A type contains no role and no run-time value. A type may be
empty: `index<0>` has no value, and `[index<0>; 0]` has one. No rule assumes that a data type has
a value; a `draw` and a `sample` need a non-empty domain (TY15), and nothing else does. *Naturals* are
`nat` and `index<s>`. **Message:** "`rational` is a specification type".

**TY2. Sizes.** A size is a term over numerals and static naturals built with `+`, `-`, `*`,
`/`, `^`, `log2( )` and parentheses. It contains no call of a function. The static naturals are:
static parameters; natural members (`M::Degree`, `F::Order`); the index of a loop or of a
comprehension over a static range, in the positions where TY10 and TY11 make it static (a size, a
static argument, a tuple position, a bound of a slice); and *static names*. A static name is
declared in one of two ways:

- in a body, by a binding `x = e` without `mut` and without a type, where `e` is itself a size
  (`half = 2^(n - k - 1)`);
- in a file module, a section or a module, by the item `nat N = e`, where `e` is a size over the
  static parameters and the static names of the scopes around it
  (`nat N = 2^(LogDegree + LogBlowup)`). It is evaluated at each instance of a member that reads
  it, is named `M::N` from outside when it is `pub`, and in a module that implements an interface
  it also defines the natural member of that name (SP8).

A specification-only static parameter is a static natural in specification items only (SP11). A
run-time value never occurs in a size. A size is *evaluated* at each instantiation, bottom up, in
the naturals: `a - b` needs `b <= a`; `a / b` needs `1 <= b` and `b` dividing `a`; `log2(a)`
needs `a` a power of two. A size that cannot be evaluated refuses the instance. A static natural
used as a value is the number it evaluates to. **Messages:** "`<e>` is not a size: `<n>` is a
run-time value; a size is built from static naturals"; "the size `<n - m>` is 3 - 8 here: a size
is a natural"; "the size `<e>` is 12 / 5 here: division in a size is exact"; "the size `<e>` is
log2(12) here: log2 takes a power of two"; "`<f(n)>` is a call; a size is built from static
naturals and the operators of sizes".

**TY3. Comparison of sizes and types.** Two sizes are equal, or ordered, as the numbers they
evaluate to. Two types are equal when they are the same after aliases are expanded and sizes are
evaluated. There is no symbolic comparison, no normal form and no decision procedure: in an
instance nothing is symbolic. An alias is its definition everywhere: in equality, in a
construction and in a pattern. At an instance a type member of a module is its definition (SP8).
The join of a type and one of its aliases, or of a type member and its definition, is that type.

**TY4. Facts.** A *fact* is what one role knows about a value at a point of control. It is not
a type parameter, and it changes no type: not of the core, and not of the source. A fact is
about a *value*: what an expression evaluates to where it stands. A name is the value it was
bound to, and a `mut` name the value it was last assigned. Two expressions that apply the same
operation to the same values are the same value: an operation on naturals, on `bool` or on a
collection, a field of a record or a position of a tuple, a row that draws nothing, a call. A
draw, a sample and a request are a new value every time. A *term* below is an expression read
as the value it is: a local name, such a name followed by fields or tuple positions
(`input.rows`), `length(t)`, an arithmetic expression (`start + count`). In a function the one
role is the role that runs it.

| Fact | Made by |
|---|---|
| a *range* `lo <= t <= hi`, `lo` and `hi` numbers (`hi` may be absent) | the type of `t` (`index<s>` gives `0 <= t <= s - 1`; `[T; s]` gives `length(t) == s`); a guard on `t` against a static term (TY9); the bounds of a loop or a comprehension, for its index; the right side of the binding of `t` (below) |
| an *order* `t < u` or `t <= u` between two terms | a guard `t < u`, `t <= u`, `t == u`; the range `a..u` of a loop or a comprehension, for its index `i` (`i < u`) |
| a *size* `length(t) == s`, `s` static | the type of `t`, when it is a `[T; s]`; a guard or a condition; the right side of the binding of `t` (below). With it `t` is accepted where a `[T; s]` is expected (TY5) |
| *nonzero* `t != 0`, `t` a field element | the type of `t`, when it is a `nonzero<F>`; a guard or a condition; the right side of the binding of `t` (below). With it `t` is accepted where a `nonzero<F>` is expected (TY5) |

The condition of an `if` makes the same facts as a guard on it (TY9), for its arms only; the left
operand of `and` and of `or` makes them for the right operand (TY9).

*A binding carries the facts of its right side.* A name bound without `mut`, `x = e`, has, at
each role that computes it, the facts that `e` has at that role where the binding stands: its
range when it is a natural, its size when it is a collection, and that it is not zero when it
is a field element. With `i: index<4>`, the name `j = i + 1` has the range `1..4`, and `j` is
accepted where an `index<5>` is expected (TY5). The type of `x` is not changed by it: `j` is a
`nat`. The name is the value of `e`, so it has the order facts of `e` too. A name bound by a
pattern has the facts that the type of its component gives.

*Scope.* A fact holds from the statement that makes it to the end of its suite, in every nested
suite; a fact made in an arm or in an iteration does not leave it. Facts are about values, so
no statement invalidates one: an assignment makes a `mut` name another value, of which the
facts of the value before are not known. So a fact about a `mut` name holds until the name is
assigned again. After a choice or a loop whose suites assign a `mut` name, the name is a value
of its own: a natural has the widest of the ranges that the arms leave it, and the accumulator
of a sum the range of the sum (TY8). *Code that does not run.* A fact is asked where an
operation is applied. In code that does not run at the instance (the body of a loop or of a
comprehension over an empty static range, the arm of an alternative that has no value) no
operation is applied and no fact is asked. *Roles.* A guard performed by a role gives the fact to
that role and to no other. A computation at a role uses the facts of that role; a statement
computed by several roles needs each fact at each of them (HO2).

*Types and facts are separate.* A name has the type written where it is bound; when none is
written, the type of its right side. A guard never changes the type of a name, and no
expression's type depends on a fact. In particular:

1. the binder of an event has the type that the event gives: the type of the payload of a send
   (TY14), the law of a draw or of a sample (EV6);
2. a `mut` name has the type written at its declaration; when none is written, the type of its
   assignments (TY10);
3. the payload that an arm of a `match` binds has the type that the alternative declares (TY13);
4. a result of an application has the type that the head of the callee declares, at the static
   arguments of the application, and so has the result of a call;
5. the range of a natural expression is a fact and not a type: a natural expression is a `nat`,
   unless it is a name, a field, an element or a result whose declared type is an `index<s>`
   (TY8);
6. where a size would come from a fact, the type is unsized and the fact is about the length: a
   slice of an unsized collection is a `[T]` (TY7).

A fact is used where an access needs it (TY7, TY8) and where a conversion needs it (TY5). After
`guard length(xs) == 8` the name `xs` is still a `[F]`: the role that guarded reads `xs[7]`, and
passes `xs` where a `[F; 8]` is expected, by the fact. What crosses to another role is the type,
never a fact (TY14).

*Is `a <= b` known* (or `a < b`) at a role? Exactly when one of:

1. the ranges decide it: `hi(a) <= lo(b)` (or `hi(a) < lo(b)`), ranges by TY8;
2. `a` and `b` are terms and the role has the order fact, or the stronger one (`a < b` for
   `a <= b`), or they are the same term (for `<=`);
3. `b` is the value `a + u` (or `u + a`) of the same value `a`; for `<`, `lo(u) >= 1`;
4. `a` is the value `b - u` of the same value `b`; for `<`, `lo(u) >= 1`.

Nothing else is tried: no transitivity, no arithmetic on both sides. A message about a fact that
is not known says how to supply it in the place where it stands: a `guard` in a body; in a
formula, a clause, a law or a row, where no guard can be written, a range, a sized type or the
condition of an `if`. **Messages:** "`<P>` computes `<xs[k]>` without a fact that `<V>` holds:
`<k>` is a `nat` …; or restrict the binder to `@<V>`"; "`<rows[i]>` reads a collection whose
length is a run-time value: `<i < length(rows)>` is not known, and no guard can be written in a
formula: take the index from a range, give the collection a sized type, or make the comparison
the condition of an `if`".

**TY5. Widening and joins.** `[T; s]` is accepted where `[T]` is expected, `index<s>` where
`index<t>` with `s <= t` or `nat` is expected, a natural where `rational` is expected, and
`nonzero<F>` where `F` is expected. Widening applies to the elements of a collection and the
components of a tuple. The *join* of two types is the least type both widen to; it is the type
of a literal with several elements, of the arms of an `if` expression, of the elements of `++`
and of a comprehension typed per element, and of a `mut` name after a choice. Every other
conversion is a named function, or one of the three conversions by a fact below. **Message:** "`<e>` is a `<[F]>`; `<[F; 8]>` is expected: write
`guard length(<e>) == 8`".

*Conversions by a fact.* Three conversions go against the widening and need a fact at the role
that computes (TY4): a `[T]` is accepted where a `[T; s]` is expected when the role has the fact
`length(t) == s` about it; a natural is accepted where an `index<s>` is expected when its range
ends below `s` (TY8); an `F` is accepted where a `nonzero<F>` is expected when the role has the
fact that it is not zero. The conversion changes no type of a name: it is made at the place
where the narrower type is expected, and that is where the refining operation is applied (§7.4). A
binding with a written type is such a place: `ys: [F; 8] = xs` gives `ys` the type `[F; 8]`.

**TY6. Literals.** A number `c` checks:

- against a type `R` of sort `Ring`, when `c` is below `R::Characteristic`: it is
  `R::from_nat(c)`;
- when that ring is a field `F` and `c` is not a multiple of the characteristic, it is a
  `nonzero<F>`, which widens to `F`; so `1 / x` and `x / 2` type, the second in odd
  characteristic only;
- against a type of sort `Group` that is not a ring, and against a sized collection of elements
  of a `Group`, when `c` is `0`: the identity;
- against `rational`.

It checks against no other type: not against a declared type, and not against a type member
(NL6). A static natural that stands where a number of a ring is expected checks as the number it
evaluates to (TY2).

*`nonzero<F>` under the operators.* `*`, `/`, `^` by a natural and prefix `-` on operands of type
`nonzero<F>` give a `nonzero<F>`. `+` and `-` on them give an `F`: the operands widen (TY5).

*The type a literal expression is checked against.* A *literal expression* is a number, or
literal expressions under the arithmetic operators `+`, `-`, `*`, `/`, `%`, `^` and prefix `-`,
or a sequence literal `[e₁, …, eₖ]` or `[v; s]` whose elements are literal expressions. It is
checked as a whole: every number in it checks against the one type, and its operators are those
of that type. It takes the type from the first of these that applies:

1. the expected type, where the context gives one: a type annotation, a parameter, a port, a
   field, a result type, the element type of a collection whose type is expected. The update
   of a `mut` name declared without a type gives none (TY10);
2. its sibling, typed first, on whichever side the sibling stands: the other arm of an
   `if … then … else`; the other operand of `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `<=`, `>`
   or `>=`; for a sequence literal that is one operand of `++`, the element type of the other
   operand. As the right operand of `*` or `/` whose left operand is an element of a group that
   is not a ring, a collection of group elements or a handle, a literal expression takes the
   `Scalar` of that group. The exponent of `^` is a natural;
3. otherwise none: when the sibling is a literal expression too, the two are one literal
   expression, and where nothing gives a type the numbers are naturals.

A number that is a natural is a `nat` with the range `c..c`. `[e₁, …, eₖ]` is a
`[T; k]`, `T` the join of the elements; `[]` is the collection of no elements: it checks against
every `[T; 0]` and every `[T]`, and where no type is expected it joins any collection (TY5). Its
type where none is expected is `[(); 0]`, and what holds of `[]` holds of every value of that
type, a declared one included: the only value of `[(); 0]` is `[]`;
`[v; s]` is `s` copies of `v`; `b"…"` and `hex"…"` are `[byte; k]`. **Messages:** "the only
literal of a group is `0`; `<1>` is not a `<G>`"; "`<2130706433>` is not below the characteristic
of `<F>`"; "`<0>` is not a `nonzero` value of `<F>`"; "`<1>` does not check against `<X::T>`: a
type member has no literals; apply the function that its interface declares for constants".

**TY7. Indexing and slices.** `xs[i]` cannot stop.

- On `xs: [T; s]` it needs `hi(i) < s` by the range of `i` (TY8).
- On `xs: [T]` it needs `i < length(xs)` known at the computing role (TY4).
- On a tuple `t` it needs `i` a static natural below the number of components, and is the
  component `i`; `t.0` is the same with a numeral. The index of a loop or of a comprehension over
  a static range is a static natural in this position (TY10, TY11).

`xs[a..b]` needs `a <= b` and `b <= length(xs)` known; an omitted bound is `0` or `length(xs)`.
Its type is `[T; b - a]` when both bounds are static, `[T; c]` when it is written
`xs[a..a + c]` with `c` static, and `[T]` otherwise; the index of a loop or of a comprehension
over a static range is static in a bound (TY10, TY11). A size never comes from a fact: a slice
of a `[T]` whose bounds are not static is a `[T]` also where facts give its bounds, and its
length is then a fact about the name that the slice is bound to. *Open (§10.2 item 28):* no
rule gives the length of such a slice, of a concatenation or of a filled collection from its
parts; until one does the fact is not made, and a read through the name needs a guard on its
length. `[[T]; k]` is `k` collections with `k`
lengths; a fact about one of them is made on a name bound to it. An operation that reads a
collection is defined on the domain these conditions describe, and it is applied only under them
(§7.4).
There is no checked access in the language: `zkc::sequence::get` and `slice` are source functions
that guard and then read. **Messages:** "`<i>` is a `nat`; an index of `<xs>` is an `index<8>`:
take it from a range, or write `guard <i> < 8`"; "`<i + 1>` can be as large as 10; `<xs>` has 10
elements"; "`<xs[0]>` reads a collection whose length is a run-time value: `0 < length(xs)` is
not known; write `guard 0 < length(xs)` before it"; "`<pair>` is a tuple; a tuple is indexed by a
static natural, and `<i>` is a run-time value".

**TY8. Arithmetic on naturals, and on `rational`.** Every natural expression has a static
*range* `lo..hi` at the role that computes it; `hi` is absent for an unbounded `nat`. The range
is a fact, not a type (TY4): a natural expression is a `nat`, unless it is a name, a field, an
element or a result whose declared type is an `index<s>`. Where an `index<s>` is expected, a
natural expression is accepted when `hi < s` (TY5).

| Expression | Range | Needs |
|---|---|---|
| a number `c`, a static term of value `c` | `c..c` | — |
| a term `t` of type `index<s>` / `nat` | `0..s - 1` / `0..`, narrowed by the range facts of `t`, among them the range of the right side of its binding (TY4) | — |
| `length(xs)` | `s..s` for `[T; s]`; `0..` narrowed by facts for `[T]` | — |
| `a + b` | `lo(a) + lo(b) .. hi(a) + hi(b)` | — |
| `a * b` | `lo(a) * lo(b) .. hi(a) * hi(b)` | — |
| `a ^ b` | `lo`: `lo(a) ^ lo(b)` when `1 <= lo(a)`; when `lo(a) = 0`, `0` if `1 <= hi(b)` and `1` if `hi(b) = 0`. `hi`: `hi(a) ^ hi(b)`, and at least `1` when `lo(b) = 0` | — |
| `a - b` | `lo(a) - hi(b) .. hi(a) - lo(b)`, not below `0` | `b <= a` known (TY4) |
| `a / b` | `lo(a) / hi(b) .. hi(a) / lo(b)`, rounded down | `1 <= b` known |
| `a % b` | `0 .. min(hi(a), hi(b) - 1)` | `1 <= b` known |
| `if c then a else b` | the smaller `lo`, the larger `hi` | — |
| `∑ x ∈ D, e` over `n` elements | `0 .. n * hi(e)`; over a static range, when the range of `e` depends on the index, the sum of `hi(e)` taken index by index | — |

The row for `a ^ b` accounts for `0 ^ 0 = 1`: the power is not monotone in its exponent at the
base `0`. A `∏` of naturals has no row: it has no range, so it is a `nat` without an upper end
and is not accepted where an `index<s>` is expected.

*A range fact on an arithmetic term.* When an expression is itself a term of the fact calculus
(TY4), an arithmetic expression over immutable names included, its range is the range that the
table computes from its parts, intersected with the range facts that the role has about its text.
After `guard 1 <= x - y` the expression `x - y` has a range that starts at `1`, so `z / (x - y)`
types; in the first arm of `if i + b < d` the index `i + b` is below `d`.

No operation on naturals stops: a subtraction or a division whose side condition is not known is
refused, and the author supplies the fact. In the model a `nat` is unbounded. A back end
represents naturals in its count type and refuses to continue, as it does when memory runs out,
when a value does not fit; it never wraps. A range whose `hi` exceeds the count type of the
target refuses the instance for that target.

*`rational`.* A `rational` context is an expression whose expected type is `rational`: the right
side of a `charge`, a ceiling, a budget, the result of a `spec def` to `rational`, an argument of
`rational` type. In it every operand is a `rational`: a natural, a size and a number are
converted, `+ - * /` are exact (`e / 2^k` is the fraction, never the rounded quotient), `^` takes
an integer exponent (`2^-128`, `(1 - e / 2^k)^q`), prefix `-` applies, and `%` is refused.
Outside such a context `a / b` on naturals is the rounded quotient of the table above; a
`rational` is compared with `<`, `<=`, `>`, `>=` and `==`. Division by a `rational` that may be
zero is not refused: a charge is a formula of the formal library, where `x / 0` is `0`.
**Messages:** "`<a - b>` subtracts naturals: `<b> <= <a>` is not known; write `guard <b> <= <a>`
before it"; "`<e>` can be as large as 5; `index<5>` is expected"; "`%` is defined on naturals, not
on `rational`"; "the exponent of a `rational` is an integer; `<x>` is a `<F>`".

**TY9. Narrowing.** A guard gives its roles the facts of its condition, read as follows. The
condition is evaluated completely first. A conjunction `c and d` gives the facts of `c` and of
`d`. A comparison is turned so that `<` or `<=` stands in it (`a > b` is `b < a`). Then, with `t`
and `u` terms (TY4) and `s` a static term:

| Condition | Fact |
|---|---|
| `length(t) == s`, `s == length(t)` | the size of `t` is `s` |
| `t < s`, `t <= s`, `t == s` | the range of `t` ends at `s - 1`, `s`, `s`; `t == s` also starts it at `s` |
| `s < t`, `s <= t` | the range of `t` starts at `s + 1`, `s` |
| `t != 0`, `0 != t` | `t` is not zero, for a field element; the range starts at `1` for a natural |
| `t < u`, `t <= u` | the order |
| `t == u` | `t <= u` and `u <= t` |

Any other condition gives no fact. A fact changes no type (TY4). A fact about a `mut` name is
about the value the name has where the guard stands (TY4).

*`and` and `or`.* `a and b` is typed as `if a then b else false`, and `a or b` as
`if a then true else b` (§4.2): `b` is typed with the facts of `a`, or with the facts of the
negation of `a` in the cases of the next paragraph, at the roles that evaluate it. So
`0 < length(xs) and xs[0] == 0` and `length(xs) == 0 or xs[0] == 0` type.

*The condition of an `if`*, statement or expression, gives the facts of the table to the roles
that evaluate it, in its first arm; its second arm has the facts of the negation, when the
condition is one comparison (turned: `not (a < b)` is `b <= a`), `not c`, or `a or b`. So a
function that must not stop reads a collection of run-time length under an `if`, and returns
`Option` where a guard would stop: `if 0 < length(xs) then Some(xs[0]) else None`.

*A static condition.* A condition is *static* when it is a comparison (`==`, `!=`, `<`, `<=`,
`>`, `>=`) of two sizes (TY2), or `not`, `and` or `or` of static conditions. The index of a loop
or of a comprehension is not a size in a condition; a static name computed from it is. An `if`,
statement or expression, whose condition is static is decided at the instance: only the arm
taken is typed, and the `if` is that arm. An absent `else` that is taken is the empty suite. A
name bound in the arm does not leave it (CT3). In a protocol body such an `if` is no choice and
has no participants (CT1). An error in an arm that no checked instance takes is found when an
instance takes it, as with any generic declaration (SP7).

**TY10. Loops.** The range `a..b` of `for i in a..b` needs `a <= b` (CT6). The index is
immutable.

- *A static range* (`a` and `b` static). A loop of zero iterations types nothing; in a protocol
  body it has no participant and is not refused for having none (CT1). The index is
  *static in the body* when it occurs there in a size, in a static argument, as a tuple position
  or in a bound of a slice: these are the places where the typing of an iteration can depend on
  it.
  1. *The index is not static in the body.* The body is typed once, with the index a natural of
     the range `a .. b - 1` and every `mut` name at the type it has before the loop. When the
     body leaves the type of every `mut` name that it updates unchanged, this is the typing of
     every iteration, and the loop is *uniform*. Otherwise the body is typed again per
     iteration, in order, each iteration starting from the types at which the one before ended,
     until an iteration leaves the types unchanged (its typing is then that of every later
     iteration) or the count is reached; the loop is *stepped*.
  2. *The index is static in the body.* The body is typed once per iteration, in order, with the
     index a static natural in each: the number of the iteration. A `mut` name that the body
     updates has, at the start of an iteration, the type it had at the end of the one before.
     The loop is uniform when every iteration types identically, and stepped otherwise.
- *A run-time count* (`b` not static). `b` has a bounded range in a protocol body (CT4). The body
  is typed once with the index in `lo(a) .. hi(b) - 1` and the fact `i < b`. Every `mut` name that
  the body updates has, at the end of the body, a type that widens to its type at the start: the
  state has one type.
- *A collection* `for x in xs`. `xs` is evaluated once. The body is typed once with `x` an
  element. In a protocol body `xs` is sized.

Two iterations *type identically* when every binder, every payload of an event, every collected
value and every updated `mut` name, at both boundaries, has the same type in both, and every
static argument of a reference has the same value in both: two iterations that instantiate
different instances of one declaration do not type identically, and the loop is stepped. Types
and static arguments are compared, never ranges or other facts (TY4). The type of a
`mut` name is unchanged by a body when it is the same type at the end as at the start; for a
`mut` name with a written type, when every update widens to that type. The distinction between
uniform and stepped changes no typing; it decides the elaboration (§7.5) and the type of a
collected name (TY16).

The type of a `mut` name is the type of its last update (or the type written at its declaration,
which then every update must widen to). The update `x := e` of a `mut` name declared without a
type has no expected type (TY6): `e` is typed as it stands and the name takes its type. So
`c := 0` on a `mut` name that held a field element makes it a `nat`; a `mut` name that is to
stay a field element is declared with its type. After an `if` or a `match` it is the join of its
types at the ends of the arms. A stepped loop costs one typing of the body per iteration until
its state closes. **Message:** "`<x>` is a `[F; 8]` at the start of an iteration and a `[F; 4]`
at its end; a loop with a run-time count carries state of one type".

**TY11. Comprehensions and binder forms.** `[e for p in D]` has the elements `e` for the items of
`D` in order; its type is `[U; b - a]` for a static range `a..b`, `[U; s]` for `xs: [T; s]`, and
`[U]` for a run-time range, an unsized collection, or with `if c`. The index of a range has the
facts of TY10. The index of a comprehension over a static range has the status of the index of a
loop (TY10): when it occurs in `e` or in `c` in a size, in a static argument, as a tuple position
or in a bound of a slice, it is a static natural there, the elements are typed one by one, and
`U` is their join; otherwise `e` is typed once, with the index a natural of range `a .. b - 1`,
also when the range is empty. The index of an empty range has no value, so every check through
it holds there. A domain is a range or a collection; a range needs `a <= b` (CT6).

`∑`, `∏`, `∀`, `∃` over `D` are the folds of §3.5 over that comprehension. `∑` needs elements of
a `Group` (a group, a ring, a field, a sized collection of them), naturals, `rational`, or a
declared type or type member with `add` and `zero`; `∏` elements of a `Ring` (a field is one),
naturals, `rational`, or a declared type or type member with `mul` and `one`; `∀` and `∃` need
`bool` and evaluate every element (they do not stop early). `⟪a, b⟫` needs two collections of one
static size, of one ring, or of elements of a group and their scalars, in that order; on points
and scalars it is the multi-scalar multiplication. `sum`, `product`, `all`, `any`, `inner` are
the same folds applied to collections. A body that can stop is allowed; the elements are
evaluated in the order of the domain and the first stop is the stop of the form. Element-wise
`+`, `-` and `* scalar` apply to sized collections of elements of a `Group`; the scalar is an
element of the `Scalar` of the elements, a ring.

**TY12. Equality and order.** `==` and `!=` apply to every data type, structurally, unless the
home module of the type declares `equal` (NL6); an opaque type member has them only where its interface declares `equal` or gives it a
sort (SP12); the two sides have a join; collections of
different static sizes are a type error. They do not apply to linear values and handles. An
operator applies to a composite (a tuple, a record, a variant, a collection) only when it
applies to every component: `==` on a composite that contains an opaque type member without
`equal` is refused in the opaque typing, with the message of SP12, so that equality does not
pass opacity through a container. `<`,
`<=`, `>`, `>=` apply to naturals (and to `rational` in specifications). **Message:** "field
elements are not ordered; compare `<F>::to_nat(<x>)`", where `to_nat` is a member of the sort
`PrimeField`.

**TY13. Records and variants.** `T{f = e, g}` builds a record; a bare field name stands for
`g = g`; the fields are evaluated in the order written; static arguments come from the expected
type or are inferred from the fields (SP6). `{r with f = e}` needs a record of freely copied
data. A record pattern binds fields; on a linear record it names every field and consumes the
value. A tuple has no or at least two components; a named component is read by name or by
position. An alternative is built `Enum::Name(e…)`. `match` is exhaustive, and an alternative has one case: a second case of one alternative is
refused. In an arm, the pattern
binds the payload of its alternative with the payload's types; a payload of another arm does not
exist there; a linear payload is linear in the arm (LN1). A name bound in an arm does not leave
it; a value leaves through a `mut` name. A pattern outside `case` is irrefutable.
A pattern nested in the payload of a case covers every value of its type; a nested pattern that
some value of that type does not match is refused. A case that is one name, which is not an
alternative of the matched variant, binds the matched value and covers every alternative that
has no case of its own; a case `_` covers them in the same way and binds nothing. A `match` has
at most one such covering case, a name or `_`, and where it stands among the cases has no
meaning; a second covering case is refused.
A record is built and matched through an alias of its type as through the type (TY3).
**Messages:** "`match` on `<T>` does not cover `<alternative>`"; "`match` on `<T>` has two cases for
`<alternative>`"; "a pattern outside `case` is
irrefutable: a name, `_`, a tuple or a record pattern"; "the pattern `<Some(0)>` in the payload
of `<alternative>` does not match every `<T>`: a pattern inside a payload covers its type";
"`match` on `<T>` has two covering cases, `<x>` and `_`: one name or `_` covers the alternatives
that have no case".

**TY14. Values that cross.** A value of a sized type received from another role (a message, a
coin, a row, a result of a callee, a value the host supplies) is decoded at its type by the
receiver, with the receiver's numbers: `[T; s]` reads `s` elements, `index<s>` refuses a number
not below `s`, `nonzero<F>` refuses `0`, a field refuses an encoding that is not canonical. A
failure stops the receiver with `reject`. This is the one stop that belongs to an event and not
to a guard. A value of type `[T]` is written and read with its length; a `nat` and a length cross
as naturals below `2^64`. *Layer C:* that a `[T]` is absorbed into a
transcript with its length.

*The type on the wire.* The type of a name bound by an event, at every holder, is the type of
the payload at the sender. No type depends on a fact (TY4), so what the sender knows about the
payload by a guard or a condition does not cross: the receivers have a `[T]`, a `nat` or an `F`
where the sender knows a size, a range or that the value is not zero. At the sender the name is
the payload itself, so the sender knows of it what it knows of the payload (TY4). A guard at
one role never changes what another role decodes, and never adds a stop at another role. A sender that wants
the receivers to have the narrower type binds the value at that type before the send
(`ys: [F; 8] = xs`, a conversion by the sender's fact, then `m <- send ys to V`): the type is
then written at the operand of the send, and with it the stop of a receiver that decodes at it.

*State of the next two paragraphs: layer C, carried. The laws of the module `zkc::layout` in
source differ from the ones stated here.*

How a value is written is given by a layout: a module that implements `zkc::layout::Layout`.
Its members write and read the leaves: a natural, an element of a `Field`, an element of a
`Group`; each reader returns `Option` of the value and the number of units it took. The field
leaf is one function over `F: Field`: it sees a whole element and may use the view of the field
over its prime field (`F::components`), so a layout for a binary field can pack bits. The writer
and the reader of every other type are generated from the leaves (§8), and the structural cases
are tuples, records, variants and collections only: a tuple and a record field by field, a
variant by its tag and payload, a collection element by element (`[T]` after its length), `bool`
and `index<s>` as naturals, `nonzero<F>` as `F`. Handles, claims and specification types are not
written. An encoding that packs across elements (the bits of a vector, coefficients of twenty
bits) is not a layout: it is a function to bytes in source, and the protocol sends the bytes.

The laws of a layout. A reader is deterministic. It agrees with the writer: reading what was
written, followed by any units, gives the value and the number of units that were written. It
accepts only the canonical prefix that the writer produced: when a reader returns a value and a
count, the units it took are exactly the units that the writer writes for that value. It leaves
the suffix. Variable lengths are framed: a `[T]` is written after its length. The serialize step
rejects a whole proof that has units left over after its last value. A reader takes at least one
unit only where it is iterated until its input is exhausted: the encoding of `()` and of an empty
sized collection has no unit.

**TY15. Laws.** The type after `draw` or `sample` names a law: the uniform distribution on that
type. A type is a law when it is finite and has a value: `bool`; `index<n>` with `0 < n`; a
field; `nonzero<F>`; a type of sort `Group`; a tuple of laws; `[L; n]` with `L` a law or
`n == 0`. `nat`, `[T]`, `index<0>`, records, variants and sealed types are not. The test is made
at the instantiation.

`draw L` and `sample L` yield a *value* of the law. There is no law defined in source: a role
that needs another distribution samples or draws units and applies a function,
`seed <- draw [byte; 32] from V to P` and then `f(seed)`; what the peer sees is then the units,
as written. Three facts are separate: that a law exists (this rule); which distribution a decoder
of a suite implements; how far that distribution is from the law. The second and third are stated
by the suite (SC5), never assumed. **Messages:** "`<index<0>>` is not a law: `index<0>` has no
value, so no distribution of total mass one"; "`<Challenge<K>>` is not a law: it has no uniform
distribution: a law is `bool`, an `index<n>`, a field, a `nonzero<F>`, a group, or a tuple or
sized collection of laws".

**TY16. Collected names.** `for … collect (ys = e, …):` binds, after the loop, each `ys` to the
values of `e` at the end of each iteration, in order. `e` is an expression over the names in
scope at the end of the body. `ys` is immutable. For a loop of static count `n`: when the values
of all iterations have one and the same type `U`, which is always so for a uniform loop (TY10),
`ys` has the type `[U; n]`; otherwise it is the tuple of the `n` values, indexed by a static
natural (TY7). The types are compared for equality (TY3): there is no join by widening here, and
nothing joins to a collection of unsized collections. For a run-time count `ys` has the type
`[U]`, and the values have one type. After a loop of zero iterations it is empty, with the
element type that the body gives `e` when the body is typed apart, for that type alone; when
the body does not type at that instance, nothing is refused and it is `[]`, which joins any
collection (TY6). Its holders are
the holders of `e` (HO2). *Layer D:* a collected handle keeps its
placement; a collected claim is consumed by the collection, which is then linear (LN1). In a clause `… at i`, `ys` is the collection, or
the tuple, of the values so far (SX5).

### 6.4 Holders

`Ρ` is the roster. `S`, `Q`, `R` are sets of roles. `Γ` maps a local name to its holders, to its
type, to the facts that each holder has about it (TY4) and to whether it is `mut`; a handle
has a placement `(H, R)` in place of a holder set.

```text
Γ ⊢ e ⇒ S          exactly the roles of S can form e; S may be empty
Γ ⊢ e ⇐ S          every role of S can form e:  Γ ⊢ e ⇒ S′ and S ⊆ S′
Γ ⊢ᵣ e : T         at role r, with the facts of r, e has type T
Γ ⊢ s ⊣ Γ′         statement s is accepted and extends Γ to Γ′
act(s)             the roles that act in s
```

**HO1. The holders of an expression.** `hold(e)` is computed on the source expression, bottom
up, before any temporary exists:

1. start with `S = Ρ`;
2. for each free local name `x` of `e` (a name bound inside `e` by a comprehension or a binder
   form is not free): intersect `S` with the holders of `x`; for a handle
   `x` placed `@H -> R`, with `H ∪ R`; for one result `y.r` of an application, with the holders
   of that result;
3. for each `data(h)` in `e`: intersect `S` with `H` of `h` instead of `H ∪ R`;
4. static parameters, static names (TY2), literals, the index of a static loop, and operations
   add nothing.

So a literal, and an operation without operands, is held by every role of the roster; such an
expression is *closed*. An expression that no role can form (`S = ∅`) is refused where it stands.
A `spec` port has no holder and is no operand of a deployed expression. **Messages:** "no role
can form `<e>`: `<a>` is held by <P> and `<b>` is held by <V>"; "<V> does not hold `<x>`, which is
held by <P>".

**HO2. Computation follows operands.** Every statement that computes fixes, on the source, the
roles that compute each of its expressions:

| Statement | Its expression is computed by | `act` |
|---|---|---|
| `x = e`, `mut x = e` | every role of `hold(e)`, each its own copy; with `@S` written, the roles of `S ⊆ hold(e)` | those roles; none when `e` is closed and cannot stop |
| `x := e` | the holders of `x`, which `hold(e)` contains | the holders of `x` |
| `guard @Q c` | the roles of `Q ⊆ hold(c)` | `Q` |
| `y <- send e from p to R` | the sender `p` alone | `{p} ∪ R` |
| `h <- send e to r as oracle<K>` | `e` by the sender | the holders of `e` that are not `r`, and `r` |
| `rows <- query h from o at ps` | `ps` by `o` and the reader | `o` and the reader |
| `open c…`, `open h at p == v` | `p`, `v` by the opener and the reader | the opener and the reader |
| `y <- C(args)`, `C(args)` | each argument by the mapped holders of its port | the mapped roles of `C` |
| `if c`, `match e`, `for … in a..b` | `c`, `e`, `a`, `b` by every participant | the participants (CT1) |
| `for … collect (ys = e)` | `e` by `hold(e)` | part of the loop |
| `return e` | each result by the holders of that result | — |

That some role can form an expression is HO1's condition, and HO1 refuses an expression that no
role can form; this rule refuses a written `@S` that is not within the holders. Inside a choice
or a loop a statement is computed by the participants among its roles only (CT1): a closed
binding, which every role of the roster can form, is computed there by the participants, and
no other role has a copy of it.

A subexpression is computed where its statement computes: a call nested in the payload of a send
runs at the sender only. The roles are never decided by later use, and no later stage recomputes
them: extracting `send f(x) to V` into a binding gives `t @P = f(x)`, with the sender written,
because `t = f(x)` would compute `f(x)` at every holder of `x`.

A statement computed by several roles is typed once at each of them, with that role's facts
(TY4); it is refused when it does not type at one of them, and when it types at one role and
not at another the refusal is TY4's and names the role that lacks the fact. *Layer D, not
implemented in stage
1:* the lines of the table for an oracle send, `query` and `open`. A component of a tuple bound from an
application has its own holders. **Messages:** "`@<S>` is not within the holders of `<e>`, which
are <P>"; TY4's.

**HO3. Where `@` stands.** After a port or a result (`x: T @S`), after a binder (`x @S = e`,
`s @P <- sample T`), after `guard`, and after `reduces` and `proves` (SX6). It never follows an
expression or an event. After an application `@( … )` is the role map (RM1). A type contains no
role. **Message:** "`@` never follows an event; place the role on the binder".

**HO4. Order.** Statements execute in order. Within one statement and one role, operands are
evaluated left to right and arguments before their call; named arguments and the fields of
`T{…}` in the order written, not in the order of the declaration; the elements of a
comprehension and of a binder form in the order of the domain; `and` and `or` evaluate
their right operand only when needed; an element-wise operation in the order of the elements.
The condition of a guard is evaluated completely before the guard decides. Each role evaluates
its own copy: among the roles there is no order of stops, and none is needed. The elaboration
keeps this order and states, per statement and role, the operations that can stop in the order
in which they can (§7.5).

**HO5. When an annotation is written.**

| Position | Written | Not written |
|---|---|---|
| Port, result | always | — |
| Binder of `=` and of `mut` | to restrict to a proper subset of the computed holders; for a `mut` handle collection that starts empty, its placement | otherwise (redundant: FM2) |
| Binder of `sample`, of `attempt` | always, one role | — |
| Binder of every other event | never: the event determines the holders | — |
| `guard` in a protocol body | always | — |
| `from` on a `send` | when more than one role that is not a receiver holds the payload | otherwise (redundant: FM2) |
| `from` on a `draw` | always | — |
| `from` on a `query` | when the data of the handle has more than one holder | otherwise (redundant: FM2) |
| Role map | for each callee role whose name the caller's roster lacks or uses otherwise | for a role of the same name (redundant: FM2) |

**Messages:** "the binder of a `sample` names its one role: `s @P <- sample T`"; "the binder of a
`send` takes no `@`: the event determines its holders"; "port `<x>` has no holders: write
`<x>: T @P`, or `spec <x>: T`".

**HO6. Agreement.** A name with several holders arises only from a shared port, a `send`, a
`draw`, a query, a shared result of an application, a closed expression, or a computation over
such names by each holder. So typing implies agreement when every role follows the protocol; the
provenance condition of the core decides the same fact again over copies. A send to several
receivers is a source of agreement among its receivers only on the assumption that the sender
follows the protocol: in an experiment it holds among roles of a side that contains the sender,
and the provenance relation of the core states exactly that.

### 6.5 Events and sites

**EV1. `<-` binds an event and nothing else.** The events are `send`, `draw`, `sample`, an
oracle send, `query`, an application of a protocol, and `attempt`. `open` is an event without a
binder, and an application of a protocol that returns nothing needs none: `C(args)` on its own
line is `_ <- C(args)`. Everything a role computes by itself is an expression and is bound with
`=`. *Layer D:* the oracle send, `query` and `open` among the events. **Messages:** "`<f>` is a function: bind it with `=`"; "`<P>` is a protocol: bind it with
`<-`"; "`<C>` returns <y>; bind its result: `x <- <C>(…)`".

**EV2. Events stand alone.** An event is the whole right side of its statement; it does not nest
in an expression, and it occurs only in a protocol body. **Message:** "an event stands on its own
`<-` line: write `x <- …`".

**EV3. Sites.** One event has one site. The sites of a definition are numbered from 0 in the
order of the text, depth first (the arms of a choice in the order written, the body of a loop
once), before any expansion. A site in a loop whose iterations are emitted in sequence (§7.5) is
one site of the source with one occurrence per iteration. The *name* of a site is the binder of
its event when the binder is
one name; otherwise the name in `#[site(name)]` on the line before it; otherwise it has none. A
site without a name is not referred to; its field in a generated record is `site<n>` (§8). Two
events of one definition do not share a name. A site of an arm that a static condition does not
take (TY9) has its number and no occurrence at that instance. *Layer D, not implemented in stage
1:* the parts of `query` and `open`. *Layer C:* a label that a line of a scheme gives a site for
a suite. The core operations that one event elaborates into are its *parts*. Below the
surface each part, and each occurrence of it in a loop whose iterations are emitted in
sequence, is a site of its own, a number; the table of sites gives its site of the source, its
part and its iteration (§7.5):

| Event | Parts |
|---|---|
| `send` to one receiver; `draw`; `sample`; `attempt`; an application; an oracle send | one, `value` |
| `send` to receivers `R₁, …` | `to R₁`, …, in the order written |
| `query … deferred` | `rows` |
| `query` | `rows`, then `opening` |
| `open` | `opening`; before it, one part `reduce k` per claim of a derived kind (§7.6) |

**Messages:** "the site of `<x> <- …` is named `<x>`; `#[site(<y>)]` names it otherwise"; "two
events are named `<x>` (lines <m>, <n>)".

**EV4. Site references.** `sites.a.….z` names the site `z` reached through the applications
named `a`, …, outermost first, starting at the protocol the clause or scheme belongs to. A site
in a loop is one site; it stands for its occurrences in every iteration. A loop is not a site: it
is named by its index variable (`at i`), which must be a name. `sites.` stands only in a clause
and in a line of a scheme. **Message:** "`<P>` has no site named `<x>`; its sites are <list>".

**EV5. Send.** `y <- send e [from p] to R`. The sender is the role written after `from`, or the
only role of `hold(e)` that is not a receiver. The sender is none of the receivers, and a
receiver is named once. `y` is held by the sender and the
receivers, with the type of the payload (TY14): a guard of the sender neither
narrows what a receiver decodes nor adds a stop to it. A handle is not sent. A send to
several receivers is one site with one part per receiver; a sender that does not follow the
protocol can send different values, and no rule of this reference detects it (HO6).
**Messages:** "`<e>` is held by <P, W>: write `send … from <P> to <V>`"; "no role other than the
receivers holds `<e>`".

**EV6. Draw and sample.** `c <- draw L from d to R`: role `d` samples a value of the law `L`
(TY15) and sends it to every role of `R`, atomically: nothing happens at `d` between the two and
the whole value is sent. `d` is not in `R`, `R` is not empty, and a role is named once in `R`. `s @p <- sample L` samples at `p`
and sends nothing. `draw` is a kernel event (`core.draw`); it is not a sample followed by a send,
which has two sites and a coin that stays secret until it is sent.
**Message:** "<V> draws and receives; a coin that nobody else receives is a `sample`".

**EV7. Attempt.** `k @P <- attempt` binds the attempt number, a `nat` held by `P`, `0` in the
program as written. The checker computes which payloads and which guard conditions depend on
`k`, through bindings, and writes the list into the declaration (SC6).

**EV8. Transcript.** The names bound with `<-` in a body, in order, are its transcript.

### 6.6 Guards and reasons

**GU1. One stopping statement.** `guard` is the only statement that stops a role. A function
stops only through a guard, its own or one of a function it calls (FN2); no row of the vocabulary
stops. In the program as written a role stops nowhere else, with one exception that belongs to
events: a received value that does not decode at its type (TY14). The steps of the tool add their
own stops to a deployed program (reading a proof, an exhausted reader, the predicate of `grind`,
a carried coin that differs, the opening checks of a commitment scheme); each has a reason of its
own in the tool's documents.

**GU2. Roles.** In a protocol body a guard names the roles that perform it: `guard @V c`,
`guard @(P, V) c`. Each named role holds the condition and performs the guard on its own copy.
The roles are never omitted and the formatter never removes them. A guard in a function has no
role: the role that runs the function performs it. A guard is accepted at any role that holds
its condition; a guard `@P` on a condition that `V` also holds is the prover's check and leaves
the verifier with none, which SC8 reports for a scheme. **Messages:** "a guard in a protocol body
names its roles: write `guard @V <c>`, or `guard @(<P>, <V>) …` if all check"; "<V> does not hold
`<c>`: `<response>` is held by <P>".

**GU3. Reasons.** `reject`: the peer or the input broke a rule. `abort`: the role's own
randomness was unlucky and another attempt may succeed. `exhausted`: the attempts, or the bound of a search, ran out.
`refused`: a bound or a precondition was violated. The reason is the same for every role that performs
the guard. The default is `reject`. A reason is a report: for every property a verifier that does
not return has not accepted, whatever the reason. A host that runs a role interactively sees one
of three outcomes: returned, stopped with a reason, or blocked (the peer stopped). A role that
waits for a message which no role sends, because its peer stopped, is blocked: it has neither
returned nor stopped with a reason.

**GU4. No result.** A guard is never removed, whatever later code uses.

### 6.7 Control and participants

**CT1. Participants.** The participants `Π` of an `if`, a `match` or a `for` in a protocol body
are the union of `act(s)` over the statements of its suites, nested control included (HO2 gives
`act`). They are computed after the holders of the body, which do not depend on them. They are
never written: `roles(…)` stands only in a protocol head. A choice or a loop in which no role
acts is refused. A loop of zero iterations is not such a loop: TY10 types no body for it, so no
`act` is computed; it has no participant and its body is nothing at the instance. Its
collection is evaluated once as in every loop (TY10): when that evaluation can stop, the roles
that can form the collection evaluate it, and act. An `if` whose condition
is static
is no choice: only its taken arm exists at the instance, and it has no participants (TY9). **Messages:** "no role acts in
this loop"; "the roles of a loop are computed; `roles(…)` stands only in a protocol head".

**CT2. Knowledge of control.** Every participant holds the condition, the matched value, or the
bounds of the range or the collection. **Message:** "<V> acts in this <branch> (line <n>) and
does not hold its <condition> `<c>`, held by <P>; send it first".

**CT3. What crosses.** (a) A name used in a suite is used by roles that hold it (HO2). (b) A name
bound in a suite does not exist after it; a value leaves through a `mut` name declared outside,
or through `collect`. (c) Every holder of a `mut` name that the suite updates is a participant;
CT2 then gives each the condition. (d) After a choice a `mut` name has the holders of its
declaration and the join of its types. (e) The index of a loop is held by the roles that hold
both bounds.

**CT4. Bound of a loop.** A loop of a protocol body has a static bound on its count: the count
of a static range, the size of a sized collection, or `hi(b)` of a run-time bound `b`, which must
have one at every participant (an `index<n>`, or a `nat` after `guard @… b <= N`). No maximum is
written. In a function a loop over `0..length(xs)` or over a `[T]` is allowed: its count is the
length of a value that exists. So is a loop over a range that a run-time natural ends: its count
is that natural, which is a variable of the cost of the function (FN7). **Message:** "the count of this loop has no static bound at <P>:
`<b>` is a `nat`; write `guard @<P> <b> <= N` first, or take it from an `index<N>`".

**CT5. Forms of control.** There is no recursion, no `while`, no `break` and no early return.
`return` is the last line of a body. In a protocol body a choice among roles is a statement: an
`if` or a `match` with suites. This rule is about control statements. An `if … then … else`
expression in a protocol body (GR2) is no choice: it is an expression of the roles that compute
its statement (HO2), and it has no participants.
A protocol loop ranges over a range or a sized collection. A search that a standard writes as
"until enough" is a loop with a bound that stops with `exhausted` when the bound is reached
without success; it does not pad its result.

**CT6. Ranges.** Every range `a..b`, of a `for`, of a comprehension and of a binder form, needs
`a <= b` known at every role that computes it (TY4): for a protocol loop at every participant,
in a function at the role that runs it. A range is never silently empty and never stops. A
range whose start exceeds its end is refused by this rule, in a function as in a protocol body.
A slice has its own conditions (TY7).
**Message:** "the range `<a..b>` is `5..2` here: a range `a..b` needs `a <= b`".

### 6.8 Role maps

**RM1. By name.** In `y <- C(args)` each role of `C` is played by the caller's role of the same
name. A role of `C` without a namesake, or to be played by another role, is written by name:
`@(O = P, R = V)`. Positional maps do not exist. The map is injective and total. The role names
of a protocol are therefore part of its interface, like the names of its ports, results, named
sites and fields: renaming them can change how callers resolve, and never changes a byte.
**Messages:** "role <O> of `<C>` has no namesake in `<caller>`: write `@(<O> = …)`"; "roles are
mapped by name: write `@(<O> = <P>, <R> = <V>)`".

**RM2. Arguments do not choose roles.** An argument is checked against the mapped port; its
holders never select the map.

**RM3. Arguments.** Value arguments are positional, in the order of the ports that are not
`spec`, or named; positional ones come first. A `spec` port takes an argument `spec name = e`,
written after the others; an argument `spec name = e` whose name is no `spec` port of the callee
is refused by this rule. A handle argument has the mapped placement of its port. The results of
an application are bound by one name (`y.r` reads result `r`; with one result, `y` is the
result) or by a tuple pattern in the order of the head. An application without results needs no
binder (EV1); written `y <- C(args)`, the name `y` names its site. **Message:** "`<C>` has no
specification port `<q>`".

**RM4. Keys are inputs.** By convention a library protocol takes keys as inputs; only a protocol
that a `scheme` closes has the role that generates them.

### 6.9 Linearity

**LN1. Use marks.** A `linear struct`, and the sealed type `Pending<K>`, is used exactly once on
every path that returns; every other type is copied freely. A collection, a tuple or a variant
with a linear component is linear. A type parameter without the bound `linear` is instantiated
only by freely copied types. A path that ends at a stop owes nothing. A path is syntactic: at a
`guard` one path ends at the stop and one continues, whatever the condition is, so `guard false`
removes no path, and no reasoning about conditions is made. *Layer D:*
`Pending<K>`; in
layer A the linear types are the `linear struct`s.

**LN2. Uses.** A use is: passing the value to a parameter or a port, returning it, matching it
with a record pattern (in the module that sees its fields), placing it in a tuple, a collection
or a linear record that is itself used once, collecting it (TY16), or, for a claim, `open`. A
value with several holders is used once by one statement, at all of them. A `mut` linear name is
consumed and assigned in one statement. A linear value has no `==` and is not used inside a loop
that is outside its scope. A specification expression may
mention a linear value (`holds(c)`, `position(c)`): that is not a use, and it neither discharges
nor duplicates the value. Both arms of a choice use the same linear names. *Layer D:* `open`
as a use, and the collecting of a claim.
**Messages:** "`<x>` (line <n>) is never opened, returned or passed on"; "`<x>` is used twice (it
was bound at line <n>); a linear value is used exactly once".

**LN3. `_`.** `_` does not match a linear value. **Message:** "`_` does not match a linear
value: open it, return it or pass it on".


### 6.10 Oracles

*State: layer D, carried; not frozen. A redesign is pending, and its
direction is settled: a claim is one handle, one position and one row, and a
deferred query at `m` positions yields `m` claims; `open` consumes the claims and applies the
kind's `Open` to what they hold (the lower handles, the positions, the rows), so that `Open`
neither reads nor consumes a `Pending<Self>`; `Residual` takes the size of the block; an
`oracle def` may take a sized collection of handles of one kind as one parent; the soundness of
`Open` is a `reduces` contract with its charges, which every implementation carries, in place of
the law `opened`; the commitment of an input handle of a derived kind is its `Send`, run by the
host of the prover; `Commitment` is completed with a combination for a `Linear` kind, coins for
an opening, and hiding, binding and extractability as properties that a goal names. Until that
redesign is written, OR4, OR5, OR7, OR9 and OR10 stand as below and are marked superseded,
pending.*

**OR1. Kinds.** A kind is a module that implements the interface `Kind` of `zkc::oracle`: types
`Data` (what a holder has), `Position` and `Row`, and a function `answer(data, position)`, which
cannot stop. The shape of a kind (the number of rows of a table, the degree of a polynomial) is
in the static arguments of the module. So `Data` is a sized type, a position of a table is an
index, and neither a send nor a query tests anything at run time. A kind is *primitive* when it
does not implement `Derived`; a scheme then names a commitment scheme for it (SC5). The interfaces
that fix the types of a kind do so by equalities in their `where` (SP4):

| Interface | Declared in | Fixes |
|---|---|---|
| `Rows<T, n>` | `zkc::oracle` | `Data = [T; n]`, `Position = index<n>`, `Row = T` |
| `Polynomial<F, d>` | `zkc::polynomial` | `Data = [F; d + 1]` (coefficients), `Position = F`, `Row = F` |
| `Multilinear<F, v>` | `zkc::multilinear` | `Data = [F; 2^v]`, `Position = [F; v]`, `Row = F` |
| `Linear<F>` | `zkc::oracle` | `Data` is a `Group` with scalar `F`, `Row = F`; handles combine (OR8); its law says that `answer` is linear in the data |
| `Derived` | `zkc::oracle` | types `Lower` and `Residual`, protocols `Send` and `Open` (OR10) |

The kinds `table<T, n>`, `poly<F, d>` and `multilinear<F, v>` are modules in source. The core
library also declares the sealed types `Oracle<K>` and `Pending<K>`, the functions `data(h)`,
`pending(h, position, row)` and `lower(h)`, and the specification functions `handle(c)`,
`position(c)`, `row(c)` and `holds(c)` on a claim. A kind whose shape is a run-time value is not
expressible (§10.2).

**OR2. Handles.** `h: Oracle<K> @H -> R`: the data is at the roles of `H`, the right to ask at the
one role of `R`; `H` and `R` are disjoint. As an operand a handle is held by `H ∪ R` (HO1).
`data(h): K::Data` is formed by the roles of `H`; it is a value of a sized type, which a
specification reads by position. Tuples and collections of handles have one placement. A handle
is passed only to `data`, `lower` (inside the module of its kind), an instance of an `oracle def`,
a port of an application, the handle operators and `collect`; it is not sent and is not a field
of a declared record. A `mut` collection of handles that starts empty writes its placement
(`mut hs: [Oracle<K>; 0] @P -> V = []`). **Messages:** "<P> holds `<h>` but <V> is its reader: <V>
cannot use `data(<h>)`"; "the handle `<h>` has one reader".

**OR3. Send.**

```text
           hold(e) = S     R = {r}     C = S ∖ R ≠ ∅     Γ ⊢ₚ e : K::Data  for the sender p ∈ C
(O-Send)  ─────────────────────────────────────────────────────────────────────────────
           Γ ⊢ h <- send e [from p] to r as oracle<K> ⊣ Γ, h : Oracle<K> @ C -> R         act = C ∪ R
```

Whoever holds the payload holds the data. An oracle is sent to one reader. `K` is a primitive or
a derived kind, written with its static arguments (`table<F, 2^k>`); an instance of an
`oracle def` is formed, not sent. The payload has the type `K::Data`, so that the data fits the
shape is typing and nothing is tested: the ideal oracle holds a value of that type; a commitment
scheme realizes the kind at that type (SC5); and the kind of an input handle, sizes included, is
a static argument of the instance and so part of the deployment identity. One send is one
commitment and one site. **Messages:** "an oracle is sent to one reader"; "`<values>` is a
`<[F; 4]>`; the data of `<table<F, 8>>` is a `<[F; 8]>`"; "the shape of an oracle is in the
static arguments of its kind: write `as oracle<table<T, n>>`".

**OR4. Query.** *Superseded, pending: a deferred query at `m` positions is to yield `m` claims.*

```text
           h placed @H -> {r}     o the role written after `from`, or H = {o}
           hold(ps) ⊇ {o, r}     ps zipped against h
(O-Query) ─────────────────────────────────────────────────────────────────
           Γ ⊢ rows <- query h [from o] at ps ⊣ Γ, rows : rows of K @ {o, r}          act = {o, r}
           Γ ⊢ (rows, c) <- query h [from o] at ps deferred ⊣ Γ, rows : …, c : Pending<K> @ {o, r}
```

A query has one opener `o`; it is written when the data has several holders. `h` may be a tuple
or a collection of handles with one placement; `ps` is zipped against it: a tuple against a
tuple, a collection against a collection of the same size; at one handle, one position gives
`K::Row` and a collection of `n` positions gives `[K::Row; n]`. The claim `c` has the structure
of `h`. A position has the type `K::Position`; nothing is tested at run time, and a position that
a role received was decoded at that type (TY14). One query is one block and one site: an exchange
of the rows `K::answer(data(h), p)` from the opener to the reader (part `rows`) and, without
`deferred`, the opening of its claims (part `opening`). Without `deferred` every row is proved;
with it nothing is proved and the claim `c` is owed. **Messages:** "the data of `<h>` is held by
<S, P>: write `query <h> from <S> at …`"; "`query <h> at <ps>`: <P> does not hold `<ps>`; draw it
`to <P>` or send it"; "a position of `<table<F, 8>>` is a `index<8>`; `<z>` gives a `index<9>`".

**OR5. Claims.** *Superseded, pending: a claim is to be one handle, one position and one row.* `pending(h, p, v)` and, inside `open`, `h at p == v` form a `Pending<K>` held by
the opener and the reader of `h`, with `p: K::Position` and `v: K::Row` held by both. Forming a
claim is an expression: no site, nothing moves. A claim in place is written on a handle whose
data has one holder.

**OR6. Open.** `open c₁, …, cₙ` takes an ordered block of claims: each `cᵢ` is a `Pending<Kᵢ>`,
a tuple or a collection of them, or a claim in place, all with one opener and one reader. It
consumes them and binds nothing. The reader stops with `reject` when a claim is false. One `open`
is one site and one opening operation of the core, whatever the kinds and the commitment schemes
of its claims; opening one claim is the block of one. A block is not empty: a protocol whose block could be
empty at an instance states the bound that excludes that instance in its `where`. `act` is the opener and the reader.
**Message:** "the claims of one `open` have one opener and one reader".

**OR7. Told and proved.** *Superseded, pending: validity is to be a `reduces` contract of `Open`, not a law of the kind.* A row from a deferred query is an ordinary value: it may be guarded,
branched on, used as a coefficient. Three statements about its claim are separate.
*Custody* is typing: a `Pending<K>` is linear (LN1) and sealed, consumed only by `open`, by
`return`, by a port of an application or by `collect`; so in every run in which the reader
returns, each claim it formed was opened or returned. *Validity* is a law of the kind: that a
successful `open` (for a derived kind, its `Open`) establishes the claimed rows, or hands on a
stated residual obligation (OR10). A goal that needs it stays open until the law is proved.
*Security* of a commitment scheme is the commit theorem of the tool. Consuming a claim proves
nothing about what was known earlier: a proof that uses a told row before its `open` accounts
for the run in which the claim is false (SX8).

**OR8. Handle arithmetic.** `h₁ + h₂`, `h₁ - h₂` and `h * c` need handles of one kind `K` that
implements `Linear<F>`, equal placements, and `c: F` held by all holders and the reader. The
result is an `Oracle<K>` with the same placement. Handles of kinds that differ in a static
argument (polynomials of different degrees) are of different types and do not combine. No kind widens
to another; a conversion between shapes of one family is a named function of a library. Nothing
is tested at run time. No site. **Messages:** "handles of `<table<F, 8>>` do not combine: the kind
is not `Linear`"; "`-` on a handle of `<poly<F, 16>>` and a `<Oracle<poly<F, 8>>>`".

**OR9. Virtual oracles.** *Superseded, pending: a parent may become a sized collection of handles of one kind.* In `oracle def F<…>(p…, c…): Rows<T, n>:` the parameters of handle type
are the *parents* and the others the *captures*. Its one line `at i: e` gives the row at the
position `i`: `i: index<n>`, `e: T`, `p[q]` is the row of the parent `p` at `q`, a position of
the kind of `p`, no `q` depends on a row, and `e` cannot stop. The shape of `F` and of each parent
is in static arguments, so nothing is tested where an instance is formed. An instance
`F(h…, c…)` is an expression that cannot stop: the parents share one placement, the captures are
held by all of its roles, its type is `Oracle<F<…>>`, a kind of its own that implements `Kind`
and `Rows<T, n>`. At a holder, `data` of an instance is the tabulated row expression. A query of
an instance is one block over its parents (§7.6). **Messages:** "the row of `<F>` reads `<p>` at a
position that depends on a row"; "the row reads `<p>` at `<i + 1>`, which can be as large as 8;
`<p>` has 8 rows"; "the shape of a kind is in its static arguments, so an `oracle def` has no
shape line and no premise; its body is the line `at i: e`".

**OR10. Derived kinds.** *Superseded, pending: as written, `Open` can neither read nor consume its claims, and the law `opened` is satisfied by no module; `Open` is to receive the lower handles, the positions and the rows, and to carry the contract `reduces @R (∀ c ∈ claims, holds(c)) to settled(residual)`.* A derived kind is a module `M` that implements `Kind` and `Derived`:
`type Lower` (the handles that a handle of the kind stands for), `type Residual` (the claims on
lower kinds that an opening leaves), the protocol
`Send roles(H, R)(data: Data @H) -> lower: Lower @H -> R`, the protocol
`Open<n: nat> roles(H, R)(claims: [Pending<Self>; n] @(H, R)) -> residual: Residual @(H, R)`,
the specification function `settled(residual)`, and the law
`opened: settled(residual) == ∀ c ∈ claims, holds(c)`. `Open` takes an ordered block; the law is
what a goal about the kind rests on (OR7). A derived kind is chosen by a static argument. A send,
a query and an `open` of a handle of `M` are written as for any kind; `lower(h): M::Lower` is
available in the module of `M` only.

**OR11. No scheme in a body.** A body names no commitment scheme, no key and no hiding; they
are a line of the `scheme` (SC5).

### 6.11 Functions

**FN1. Local code.** A `def` is deterministic and free of roles: it contains no event, no `@`
and no `roles`. Its statements are `Binding`, `MutDecl`, `Update`, `Guard`, `If`, `Match`, `For`
and `Empty`. **Message:** "an event stands only in a protocol body; a `def` runs inside one
role".

**FN2. When a function can stop.** A function can stop exactly when its body

1. contains a `guard`;
2. calls a function that can stop, or a member that its interface declares `partial`.

This is read on the text of the body at the instance, before any evaluation: a body that
contains a guard, or a call of a function that can stop, can stop also where short-circuit
evaluation never reaches it, so `false and fail()` can stop (for FN5 and SP9, and for `act` of
HO2). An arm that a static condition does not take (TY9) is not part of the body at that
instance.

Nothing else stops. No row of the vocabulary stops; operators, indexing, slices, literals,
records, comparisons, mathematical forms and instances of an `oracle def` are total, because
their side conditions are facts (TY7, TY8). A checked operation is a function in source: a guard,
then a total operation (`zkc::sequence::get`, `zkc::coset::coefficients`); a decoder
returns `Option` and does not stop. Whether a function can stop is computed, shown by the tools
and part of a module's interface; it is written only as `partial` on an interface member (SP9).

**FN3. Where a function may not stop.** The formula of a `relation`; an expression of a clause;
a `law`; the row of an `oracle def`; a function named `at` (NL6); a `spec` argument; a definition
with a kernel (FN5). The function named after `by` in a `knowledge` or a `zero_knowledge` clause is a `def` and may stop (SX6).
**Message:** "the formula of `<R>` can stop; a relation needs an expression that cannot stop".

**FN4. Body and result.** A body is one expression, or statements followed by `return e`
(GR1). `mut` names and updates are local to the function. A function without `->` returns `()`.

**FN5. Kernels.** `#[kernel("name")]` on the line before a `def` or a member definition that has
a body attaches an implementation: native code that a back end runs in place of the body. A
kernel stands only on deployed code: not on a `spec def`, and not on a member that its interface
declares `spec`. The body is the meaning: removing the attribute changes no result, no proof byte
and no identity; the kernel is recorded beside the module and is in no identity (§7.1). A target
without the kernel runs the body. The body cannot stop; a function whose guard needs a costly
test calls a function with a kernel for the test (`guard not contains(domain, zeta)`). That the
kernel computes the body is an assumption that carries the kernel's name: every receipt that
rests on the definition lists it, and every build tests it by running both on the same inputs. A
binding to a row has no kernel: the row is its implementation. **Messages:** "`<f>` can stop; a
kernel is attached to a `def` whose body cannot stop"; "a kernel is attached to a `def` with a
body"; "`<thing>` is a specification function: it runs nowhere, and a kernel is an implementation
of deployed code".

**FN6. Calls.** Arguments are positional or named, positional first; a named argument names a
parameter. A call of a function nests in any expression. `;` stands only in the arguments of a
relation (SX3).

**FN7. Cost.** The *cost* of a `def` at an instance is a count of applications of rows. Nothing
is recursive (NL1), so it is a formula, computed from the body bottom up, in the static
parameters of the instance, which are numbers there, and in the lengths of the inputs of
run-time length.

| Construct | Cost |
|---|---|
| an application of a row: an operator, a literal, a form or a call that §7.4 or a `primitive` binding makes a row | 1 |
| a call of a function with a body | the cost of the callee at the instance called, its length variables replaced by the lengths of the arguments |
| operands, arguments, statements in sequence | the sum |
| `if`, `match`, `a and b`, `a or b` | the cost of the condition or of the matched value, plus the largest cost among the arms; for a static condition, the arm taken |
| a loop, a comprehension or a binder form over a static range or a sized collection of `n` items | `n` times the cost of the body; for a stepped loop the sum over its iterations; a binder form adds `n` for the fold |
| the same over a collection of run-time length, or over a range whose end is a run-time natural | the length, or the natural, times the cost of the body. Where the range of the length has an upper end at that point (TY8), by the type, a guard or a condition, that end stands for it; otherwise the length is a variable of the formula |
| `guard c` | the cost of `c` |

The cost is *closed* at an instance when no variable is left in it: every length that it depends
on is bounded. Four quantities are kept apart, and none is reported as another:

1. the cost of a local algorithm: this formula;
2. the cost of extraction or of simulation: the calls of the adversary, the rewinds and the
   oracle queries, with the success probability, under the experiment of the theorem of the
   formal library that a clause is used with (SX6);
3. native cost: time, memory and the size of operands on a target. It is not claimed: a count of
   rows is not a running time, and one application of a row on naturals counts 1 whatever the
   size of its operands;
4. the resources of the compiler itself: instantiation, the typing of stepped loops, the
   evaluation of laws. Exhausting one of them is an incomplete check, never a refusal of the
   program and never a proof (SP10).

The cost is read in one place: an extractor or a simulator written in source is admitted when
its cost is closed at the instance, and the receipt states the formula beside the cost of
acquisition that the theorem gives (SX6, GL5). It selects no code, and it does not decide whether
a law is evaluated (SP10). The details of the accounting (what a generated function, a
construction and a refining row count) are settled with layer B, which reads the cost.

### 6.12 Specification

*State: SX1, SX2 and SX4 are layer A and frozen. SX3 and SX5 to SX9 are layer B, carried:
the statement of a property is the definition of its entry in the
formal library, which this section renders and does not define; extractors and simulators
are deployed functions whose local cost is closed; a tree function states the
implication of special soundness and one-run extraction an obligation bounded by the charges;
the abilities of a simulator are permissions, checked at the goal (GL3); a relation may
carry a `where` and is not bound to an asset; with several clauses of one kind
each goal names the clause it reads.*

**SX1. Three layers.** The program: protocols, functions, records, schemes, entries. The
specification: `relation`, `spec def`, `spec type`, `spec protocol`, `spec` ports and arguments,
`spec` static parameters, `spec for`, `law`. The request: `goal`.

**SX2. Erasure.** Erasure is a projection, not a deletion in the source. The *deployed program*
of a scheme is what the steps of the tool run: the closure of the scheme's protocol instance
through deployed references (§7.1 item 8), the functions that the lines of the scheme name, and
the deployed members of the modules that those lines name (SC5). Specification items, goals,
kernels and the specification-only members of a module (a `spec def` member, a law) are outside
it: they are recorded beside the module and are in no identity of a proof. So changing or
removing any of them changes no role program, no entry record and no proof byte. To that end: a
deployed definition refers to a specification item only inside a `spec` argument, and gives a
specification-only static parameter only in a specification argument (SP11); a member that
an interface declares `def` is deployed code in every implementing module (SP8); inference of
static arguments, sizes, `where` constraints and facts never read a `spec` port, a `spec`
argument or a specification-only static parameter (SP4, SP6, SP11); and the deployment identity
is the hash of the projection (§7.1). **Message:** "`<f>` is a specification function; deployed
code cannot call it".

**SX3. Relations.** A relation is a specification function to `bool` with a split: statement
parameters before `;`, witness parameters after it. Its formula is one expression that cannot
stop; it may call functions, specification functions and relations and use the mathematical
forms. A relation has a formula or is bound to `external`; it is not bound to an asset (NL9). Its
head may carry a `where` over static terms (SP4), which is a condition of every application. An
application has as many arguments on each side as the definition. The short application `R(a…)`,
without `;` and the witnesses, says that some witness exists; it stands only at the top of
`reduces`, `proves`, `through` and `knowledge`, where the statement generator introduces the
quantifier. A clause that takes a relation takes any `bool` specification expression.
**Messages:** "`<R>` takes 2 statement arguments and 1 witness argument"; "`<f>` is not a
relation; its arguments are separated by `,`".

**SX4. Specification ports.** `spec p: T` is a port that no role holds. It is in scope only in
specification expressions. Every application binds every `spec` port of its callee (RM3).
**Message:** "`<C>` has the specification port `<p>`; write `spec <p> = …`".

**SX5. Contracts.** `spec for P:` stands once, in the module that defines `P`. Contracts are
typed at each instance of `P`. In scope are the static parameters and the ports of `P` under
their own names. The results are added in `ensures` and on the `to` side of `reduces`. They
are not in scope of a `knowledge` clause: over several runs the results differ, and an extractor
reads them through `runs[i]`. A clause `… at i` is typed at every boundary of the loop `i`: in scope are the names
visible at the loop with their types at that boundary, the index (for a static loop, the number
of the boundary, from `a` to `b` inclusive), and each collected name as the collection of the
values so far. A name with several holders denotes the agreement; a clause never selects a copy.
A port and a result do not share a name. A linear port or result may be mentioned (LN2).

**SX6. Clauses.**

| Clause | Statement | Typing beyond "`bool`, cannot stop, in the scope of SX5" |
|---|---|---|
| `requires E` | a fact before the run | — |
| `ensures E` | a fact when the run returns | — |
| `invariant E at i` | a fact at every boundary of the loop `i` | `i` is the index of a `for` of the body |
| `reduces @D R to S` | the statement `R` about the inputs becomes the statement `S` about the results | the deciding role `D` (below) |
| `proves @D R` | `reduces R to true`: the protocol decides `R` | as `reduces`; the protocol returns nothing to `D` except claims |
| `through T at i` | the statement to which `R` has been reduced at each boundary of the loop `i` | follows a `reduces` or `proves` |
| `knowledge R′(a…) by e [or Q(b…) by f]` | on a tree of accepting runs, `e` returns a witness of `R′(a…)`, or `f` one of `Q(b…)`; or, reading one run, the deciding role returns while `e` gives no witness with probability at most the charges | the extractor (below) |
| `knowledge R′(a…) by external("name") [or Q(b…)]` | the same statement, made in the formal library under `name` | `R′(a…)` and `Q(b…)` are typed; nothing else is checked, and a goal that uses the clause is reported as resting on `name` (GL5) |
| `zero_knowledge by s using π…` | the view of one role is what `s` returns | the simulator (below) |
| `zero_knowledge by external("name")` | the statement made in the formal library under `name` | nothing is checked, and a goal that uses the clause is reported as resting on `name` (GL5) |
| `charge sites.x <= e` | the probability lost at the site | the site is a `draw`, an application or an `attempt`; `e: rational` over static terms: no port, result or local name occurs in it |

*The deciding role.* In `R(a…; w…)` the values `a…` are in statement positions and `w…` in
witness positions; in any other expression every value is in a statement position. A role *can
decide* a clause when it holds every port and result in a statement position (for the `data` of
a handle: when it is the handle's reader) and holds none in a witness position; `spec` ports
count for neither. The deciding role is the role written after `@`, which must be able to
decide; it may be omitted when exactly one role can. At an application of a callee that has a
`reduces` or `proves` clause, inside a protocol that has one, the callee's deciding role is
played by the caller's deciding role; a callee whose rejection the caller must survive returns a
`bool` instead. A label names a clause for a goal (`clause = label`).

*The extractor.* In a `knowledge` clause the relation is applied to its statement arguments only
(the short application of SX3): the witness is what the extractor returns. For

```text
relation R′(x₁: A₁, …, xₙ: Aₙ; w₁: W₁, …, wₘ: Wₘ)
```

the extractor of `knowledge R′(a…) by e` has the signature

```text
def e<σ>(x₁: A₁, …, xₙ: Aₙ, runs: P::Runs<k₁, …, kⱼ>) -> W
```

with the types at the static arguments of the application; `W` is `W₁` when `m = 1` and the
tuple `(W₁, …, Wₘ)` otherwise; `σ` are static parameters of `P`, under their names; `P::Runs` has
one natural per draw of `P` (§8). An extractor is an algorithm with a stated cost. It is a `def`
and not a `spec def`, so it calls no specification function and nothing bound to `external`; it
is admitted when its cost at the instance (FN7) is closed, and the receipt states that formula. A
search over a field then appears as a cost of the order of the field instead of disappearing. A
function that is not of this form is not named after `by`: the clause is written
`by external("name")`.

What the clause states depends on the naturals of `Runs`:

- *Every `kᵢ` is at least 2: a tree function.* The source states the implication of special
  soundness: on every tree of accepting runs of the declared shape, `e` returns and
  `R′(a…; e(a…, runs))` holds. So `e` may contain a `guard` whose condition the tree guarantees
  (two different challenges have a non-zero difference). The knowledge extractor, its joint
  experiment, its success probability and its cost are not stated in source: they are the
  theorem of the formal library applied to that implication, and the hypotheses of the theorem
  (the access to the prover, the shared prefixes, the distinct challenges, the sizes of the
  challenge spaces) are checked or listed in the receipt. A `kᵢ` larger than the number of
  values of the law drawn at site `i` is refused: no tree has that many different values there.
  Trees of a fixed shape are one profile; the general access model stays in the formal library.
- *Every `kᵢ` is 1: one run.* `e` reads one accepting run. The statement "the deciding role
  returns and the output of `e` is not a witness with probability at most the charges of the
  contract" is itself the obligation: the charges (SX8) are the bound that the clause claims,
  not a proof of it.

Naturals that are neither all 1 nor all at least 2 are refused. With `or Q(b…) by f`, `Q` is a
relation applied to its statement arguments, the alternative has a witness, and `f` is its
function, of the same form as `e` for `Q`; the conclusion is then about `R′(a…; e(a…, runs))` or
`Q(b…; f(b…, runs))`. A predicate of the statement alone is not an alternative: it is written as
a `requires`.

`P::Runs` is defined only for a protocol none of whose draws is in a loop, in a choice or inside
an application (§8). An extractor that rewinds a loop of challenges needs a tree of runs whose
depth is the count of the loop, which has no type yet (§10.2). For such a protocol, and for any
extractor that is not a `def` with a cost, the clause is
`knowledge R′(a…) by external("name") [or Q(b…)]`: the statement, the alternative included, is
one of the formal library.

*The simulator.* In `zero_knowledge by s using π…` the simulator has the signature

```text
def s<σ>(inputs: P::Inputs<C>           the inputs of the role C whose view is simulated
        [, coins: P::Coins<C>]          exactly when π has `coins`
        [, trapdoor: P::Coins<O>]       exactly when π has `trapdoor`; O ≠ C
        [, randomness: L])              at most one more parameter; L is a law (TY15)
    -> P::Received<C>                   without `programming`
    -> (P::Received<C>, P::Coins<C>)    with `programming`
```

Like an extractor it is a `def`, admitted when its cost at the instance is closed (FN7), and the
receipt states that formula. The abilities after `using` are what the simulator is given; the
list is left out when it is given none. `coins`: the simulator is given the coins of `C`, sampled as an honest `C`
samples them. `programming`: the simulator chooses the coins of `C`, and the experiment programs
the random oracle to return them; it excludes `coins`. `trapdoor`: the simulator is given the
coins of the role `O` of a setup. The last parameter is the simulator's own randomness: its type
is a law, and the experiment samples it; a simulator that needs several values takes a tuple, one
that needs none has no such parameter. The abilities are permissions: the property and the stage
of a goal bound what a simulator may be given, and a simulator need not use what it is allowed
(GL3). A statement that this signature cannot express is written
`zero_knowledge by external("name")`, without `using`, and its assumptions are visible in the
receipt: zero knowledge against a verifier that deviates in an interactive run is one, because
the signature has no argument for the verifier's strategy, and a simulator that runs in expected
time is another. As the formal library states honest-verifier zero knowledge: for inputs that satisfy
the hypotheses (SX7), the distribution of the coins of `C` together with what `C` receives in a
run with the other roles honest is the distribution of the coins together with the simulator's
result.

**Messages:** "<P>, <V> could each decide this clause: write `proves @<V> …`"; "`<Check>` is
decided by its role <V>, played here by <D>; this clause is decided by <V>"; "the extractor
`<extract>` takes the statement parameters of `<DLog>` and the runs: `def extract(base: G,
point: G, runs: X::Runs<k…>) -> F`"; "`<extract>` returns a `<G>`; the witness of `<DLog>` is a
`<F>`"; "a `knowledge` clause applies a relation to its statement arguments only"; "`<Q>` has a
witness: write `or <Q(b)> by f`"; "`<Anything>` has no witness parameter: a predicate of the
statement is a `requires`, not an alternative"; "`<search>` is a specification function: the
function after `by` is a `def` with a cost; for a statement of the formal library write
`by external(\"…\")`"; "the cost of `<search>` is not closed: it grows with `length(<xs>)`, which has no bound";
"`Runs<3>` asks for 3 different values of a `bool`, which has 2"; "the naturals of `Runs` are
all 1, for one run, or all at least 2, for a tree"; "`<simulate>` returns a `<F>`; it returns
`<X::Received<V>>`"; "the last parameter of `<simulate>` is its randomness, sampled by the
experiment: `<nat>` is not a law"; "a simulator is given the coins (`coins`) or chooses them
(`programming`), not both".

**SX7. What a contract says in each property.** A property is an experiment with an honest side
(GL1). Its statement is the definition of its entry in the formal library; the table and the
examples below render which clause enters it and how, and where a rendering and the entry differ
the entry governs. A clause enters the statement of a goal as a hypothesis or as a conclusion:

| Property | Honest side | Hypotheses | Conclusion |
|---|---|---|---|
| `completeness` | every role | every `requires`; the left side of `reduces` or `proves` written in full, `R(a…; w…)`, of the inputs | every role returns; every `ensures`; the `to` side of `reduces` |
| `soundness` | the deciding role | the `requires` that are available (below) | when the deciding role returns, `R(a…)` holds for some witness, or, for `reduces`, the reduced statement is false, except with probability at most the charges |
| `knowledge_soundness` | the deciding role | the same | the theorem of the formal library applied to what the clause states: for a tree function the implication of special soundness, for one run the obligation with the charges as its bound (SX6) |
| `zero_knowledge` | every role but the simulated one; a role that the scheme declares `offline` and whose coins are a `trapdoor` is on the honest side | the `requires` that are available; the left side of `proves` in full | the statement of the simulator (SX6) |
| `honest_verifier_zero_knowledge` | every role | the same | the same, with the coins of the simulated role honest |

*Availability.* A `requires`, an `ensures` or an `invariant` is part of the statement of an
experiment exactly when every value it names is held by the honest side of that experiment or is
a `spec` port; otherwise it is absent from that statement.

*Several clauses.* When a contract has several `reduces` or `proves` clauses, or several
`knowledge` or `zero_knowledge` clauses, each property reads the clause that its goal names by
its label (GL2, GL3). A promise pair is two labelled clauses, `proves exact: Exact(a…; w…)` for
completeness and `proves near: Near(a…; w…)` for soundness; a `through` line belongs to the
`reduces` or `proves` clause before it. No declaration pairs two relations.

*`proves` in full and short.* `proves R(a…; w…)` binds the witness positions to names that the
prover holds. For completeness it is the hypothesis "the prover's inputs are a witness"; for
soundness only "a witness exists" is read. `proves R(a…)`, without the witness, says the same to
soundness and gives completeness no hypothesis: its completeness statement then needs a
`requires` that says what the honest prover holds.

One example for each case.

```text
proves SameLog(g, h, u, v; x)
    completeness   if u == g * x and v == h * x, the verifier returns
    soundness      if the verifier returns, some x has u == g * x and v == h * x
    no `requires` is needed: the full application is the honest prover's hypothesis

requires data(codeword) == tabulate(p, domain)       names data that P holds
proves @V Near(p, domain, data(codeword))            every position is a statement position
    completeness   (P is honest: the `requires` is a hypothesis) if the table is the
                   tabulation, the verifier returns
    soundness      (V alone is honest: the `requires` is absent) if the verifier returns, the
                   table is near, except with the charged probability

requires R::table(state) == restrict_prefix(p, prefix)       state is P's, p is a `spec` port
ensures  R::table(residual) == restrict_prefix(p, point)
reduces @V PartialSum(p, prefix, claim) to PartialSum(p, point, value)
    completeness   from the `requires` and the left statement: both roles return, the `ensures`
                   and the right statement hold
    soundness      if the left statement is false and the verifier returns, the right statement
                   is false, except with the charged probability

proves DLog(base, point; scalar)
zero_knowledge by simulate using coins
    for point == base * scalar: the verifier's coins and what it receives are distributed as
    its coins and `simulate(inputs, coins, r)` for a uniform r
```

A `requires` is not checked at admission (an author who wants the check writes a guard). The
receipt shows each hypothesis, as source text and as the function it elaborates to, with the
exact domain of the statement proved, and with a witness that the hypotheses are satisfiable or
the mark "unwitnessed"; satisfiable hypotheses are not presented as coverage (GL5).

**SX8. Charges.** A charge is a `rational` over static terms (TY8): static parameters, members
of static things, numbers. The charge of a `draw` is the probability that the reduced statement
becomes true there. The charge of an application is computed from the callee's charges and the
counts of the loops around them; a written charge on an application replaces it with a smaller
one. The charge of an `attempt` is the probability that one attempt aborts. A charge at a site
between a deferred query and the `open` of its claim is stated for the runs in which the claim
may be false. The charges of a contract are also the bound that a `knowledge` clause claims
when it reads one run (SX6). **Messages:** "`sites.<x>` is a send; a charge belongs to a draw, an application or
an attempt"; "a charge is over static terms; `<p>` is a port of `<X>`, a run-time value".

**SX9. Generated members.** A protocol, a scheme and a layout module have generated members,
named through `::` (NL3 c) and nowhere declared. §8 lists every one with its definition.

**SX10. Three judgments.** A build makes three judgments about a program and keeps them apart:

1. *Admission*: whether the program is admitted for execution. Every rule of this reference
   that refuses a program decides it, the two judgments below excepted.
2. *Law coverage*: for each law and each instance at which it is an obligation, one of: proved;
   decided true by evaluation; found false; not decided within the budget; not attempted (SP10).
3. *Claim validity*: whether the claim of a goal is established (GL5).

Specification material (specification items, laws, goals, the values of specification-only
static parameters) may change the second and the third judgment. It never changes the first,
and it changes no identity (SX2). A law found false is an error of the build by policy: the
build fails, and the role programs and the identities are what they would be without the law. A
law that is not decided stays an obligation and is never reported as holding. No tool reports
one judgment as another: an admitted program is not a covered law, and a covered law is not an
established claim.

*What admission presupposes.* Three things are judged of a source, in this order: that it is
*well formed*, which is required of every program, its specification items included: every name
resolves (NL3), every call and application has the arguments that its callee declares, and
every application gives the `spec` arguments (SX4) and the specification-only parameters (SP11)
of its callee; that its specification types; and that its deployed program is admitted. A
specification item that is not well formed, or that does not type, is refused as any item is,
by the rule that fails. The first judgment of the list above, and the sentence that
specification material never changes it, are about the third of these, among specifications
that type: adding, removing or changing a specification that types changes no role program, no
identity and no admission of the deployed program.

### 6.13 Schemes

*State: layer C, carried; not frozen. Everything a step runs is
deployed code; the site of a key has exactly the type of the key; a scheme does not
close a specification-only static parameter; the witness of a scheme holds the data and
the commitment state of every input handle; an index is a static argument or an input
handle. Pending: the schedule of the Fiat–Shamir step, with a label for `absorb` and
`squeeze` and what a line of a scheme may change in it; what each step relies on in
`Commitment`, `Suite` and `Layout`. The `commit` lines are layer D.*

**SC1. Subject.** `scheme S = P<…>:` closes one protocol instance: every static parameter that is not
specification-only has an argument (a goal gives the others, SP11), and a natural argument is a static term without free names. A scheme states only what
is deployed, one line per step of the compiler. A scheme has no static parameters; a
configuration shared by schemes is a module (SC5).

**SC2. Role kinds.** A role named by `offline` runs before the run; a role named by `ideal` is a
trusted party of the run, whose functionality the host connects; every other role is online.
Offline roles are ordered as written. An offline role receives only from earlier offline roles.
What an offline role sends to an online role is public. **Messages:** "<S> is offline and
receives `<x>` from <P>, which is online (line <n>)"; "`ideal R` has no right side: the
functionality of an ideal role is connected by the host".

**SC3. Prover and verifier.** The line `prover P` is allowed in every scheme and is checked.
Without it the two are computed, on the closed instance, by this procedure:

1. *Flows.* Collect every exchange (a `send`, an oracle send, the rows of a `query` from the
   opener to the reader) and every `draw` of the instance, through applications, each role
   mapped through the role maps to a role of the scheme's protocol.
2. *Candidates.* `E` is the set of online roles that send to an online role. `D` is the set of
   online roles that draw to an online role. Flows from or to offline and ideal roles do not
   count.
3. *`derived` and `authored`.* Exactly two roles are online. `E` and `D` have at most one role
   each, and not the same role. The prover is the role of `E`; when `E` is empty, the role that
   is not in `D`. The verifier is the other online role. When `E` and `D` are both empty the
   scheme states `prover P`. A written `prover P` must name the computed role.
4. *`interactive`.* Nothing is computed. A scheme that a goal names states `prover P`; the
   verifier is then the other online role when there are two.

**Messages:** "under `derived` only the prover sends: <P> sends `<x>` (line <m>) and <V> sends
`<y>` (line <n>)"; "<P> sends `<m>` (line <a>) and draws `<c>` (line <b>): the role that sends is
the prover and the role that draws is the verifier, and under `derived` they differ"; "cannot
tell the prover from the verifier of `<P>`: no online role sends to the other and none draws;
write `prover P`"; "`prover <V>` contradicts the protocol: <P> sends to the other online role, so
the prover is <P>"; "under `derived` exactly two roles are online; <S, P, V> are …".

**SC4. Statement and acceptance.** The statement is, in this order: the inputs held by both the
prover and the verifier, in the order of the signature; for every input handle that the verifier
reads, its commitment (the kind of the handle, sizes included, is a static argument of the
instance); the `context` lines, in order. The witness is the rest of
what the prover holds and, for each input handle whose data the prover holds, the data and the
state that its commitment returned. An input that the verifier holds alone is marked `private` under `derived`
and `authored`; it is not in the statement. The commitment of an input handle is formed by the
host of the prover before the run, with the scheme of its kind and the pinned keys. A statement
component of type `[T]` is absorbed with its length (TY14). No line states an acceptance: the
verifier accepts when its program returns. What the verifier's program returns is the reduced
statement, and what the prover's returns the reduced witness; a protocol that decides returns
nothing. A protocol that returns claims is a reduction whose reduced statement includes them; a
goal on its scheme says how they are settled (GL2). The index of a preprocessing argument is a
static argument of the instance or an input handle: the commitment of the handle, formed by the
host before the run, is the verification key. A role that computes an index inside the run is
not supported. **Message:** "`<x>` is held by <V> alone;
under `construction derived` such an input is `private`".

**SC5. Lines.**

| Line | Requires | When absent |
|---|---|---|
| `construction derived(S)` | `S` is a path to a module that implements `zkc::construction::Suite`: a suite in source at its static arguments (`HashChain<Keccak256, Fr>`), or a suite of the catalogue, bound once in `zkc::suites`; SC3; every `draw` between online roles is of a law that the suite decodes from its units: its challenge field `S::Challenge`, `nonzero` of it, `bool`, `index<n>`, and tuples and sized collections of them, each with the distance from the law that the suite states. A draw of any other law (another field, a group) is not derived: the protocol draws units and applies a function | refused: a scheme has one `construction` line |
| `construction interactive` | no `grind`, `retry`, `samples` and `layout` line | — |
| `construction authored` | no `grind` and `samples` line; SC3 | — |
| `prover P` | SC3 | computed, or required |
| `offline R, …`, `ideal R, …` | roles of the roster, each named once | every role is online |
| `context n: T` | `n` is not a port; the host supplies the value once; the protocol does not compute with it | no context |
| `commit K with S` | `K` is a kind pattern: a primitive kind with `_` for any argument; every primitive kind that the closed protocol sends or takes as an input handle matches exactly one such line. `S` is a path to a module that implements `zkc::commitment::Commitment<K′>`; it may go through a member of a configuration module (`C::Commitment`). The configuration of `S` is its static arguments. Those that the line does not write are found, for each kind `K″` that the line covers, by matching `K′` against `K″` (SP6): `commit table<_, _> with Tree<Keccak256>` covers tables of every row type and size, and a kind that `S` cannot realize is refused there | refused when the protocol sends an oracle, except under `interactive`, where the oracle stays ideal |
| `commit K with S(prover_key = sites.x, verifier_key = sites.y)` | the same; each key is a site of a send of an offline role. A key is written exactly when its type, `S::ProverKey` or `S::VerifierKey`, is not `()`, and the site has exactly that type. A scheme whose one key serves several shapes takes the maximum as a static argument of its own (`Kzg<E, MaxDegree>`), so that the type of its key does not depend on the shape | — |
| `commit sites.x with S(…)` | `sites.x` is an oracle send; replaces the kind line for that send | the kind line applies |
| `pin sites.x = H:d` | `sites.x` is a send of an offline role; `H` is a path to a module that implements `zkc::hash::Hash`; `d` has `H::Size` bytes and is the digest of the value in the canonical layout of its type | supplied by the proposal file; refused when neither has it |
| `grind b bits at sites.x, …` | each site is a `draw` from the verifier to the prover; `b` is static | no grinding |
| `retry N from sites.k` | `sites.k` is an `attempt` of the prover; `N` is static; every guard with reason `abort` is in the region that the attempt starts | one attempt |
| `samples derived by f` | `f` is a deployed `def`, neither `spec` nor bound to `external`, from the prover's secret inputs, the statement, a site and the attempt number to the units of each law the prover samples | fresh entropy |
| `layout L` | `L` is a path to a module that implements `zkc::layout::Layout`; `carry sites.c`: a drawn value the proof carries; `recover sites.m by f`: a message before it that the proof omits, which `f`, a deployed `def`, computes from the statement, the carried value and later messages | the layout `zkc::layout::canonical` |

*What a step runs is deployed code.* The functions named by `samples derived by` and
`recover … by`, and the members that the commit, Fiat–Shamir and serialize steps apply in the
commitment, suite, layout and kind modules that a scheme names, are deployed code: none is a
`spec def` and none is bound to `external` (SP8, SX2). **Message:** "`<recompute>` is a
specification function; `recover … by` names a function that the verifier runs".

**Messages:** "`sites.<x>` is a send of <P>, which is online; only sends of offline roles are
pinned"; "no `commit` line matches `<kind>` sent at `sites.<x>`"; "`construction interactive`
admits no `<grind>` line"; "the suite of `derived` is a path to a module that implements
`zkc::construction::Suite`; a catalogue suite is a module of `zkc::suites`"; "`<c>` draws a
`<G>`; the suite `<S>` decodes its challenge field `<F>`, `nonzero` of it, `bool`, `index<n>`,
and tuples and sized collections of them. Draw units and apply a function"; "`<Tree>` does not
realize `<table<F, 6>>`: its argument `<k>` is not determined by `Commitment<table<T, 2 ^ k>>`";
"`<Kzg<E, 8>>` has a prover key of type `<[G; 9]>`: write `prover_key = sites.x`, a pinned send
of an offline role"; "the digest of `pin sites.<k>` has 2 bytes; `<Sha256>::Size` is 32".

**SC6. What a scheme generates.** The members of §8, and the declaration (§7.8). The declaration
records, beside the lines, the computed prover and verifier, the statement, the stages the scheme
has (GL2), and the list of payloads and guard conditions that depend on the attempt number (EV7);
every receipt of the scheme shows that list.

**SC7. Proposals.** A proposal file given to the compiler completes the lines that may be
proposed: pins, a layout among those the scheme admits, `grind` bits. It adds no other line.

**SC8. A verifier that checks nothing.** A scheme whose verifier performs no `guard` and no
`open`, and reads no row with an undeferred `query`, in its protocol or in a protocol it applies,
is reported: such a verifier returns in every run. It is a report and not a refusal: a protocol
that only moves values is legal. The tools print, per role, what each statement of a protocol
makes that role compute and whether it can stop there, which shows a check or a fold that
stands at the wrong role. **Message:** "scheme `<S>`: the verifier <V> performs no guard and no
`open`: it accepts every run".

### 6.14 Goals

*State: layer B, carried; not frozen. A goal gives the
specification-only static parameters; the abilities of a simulator are checked against the
property and the stage, as permissions; a goal names its clause when the contract
has several; a ceiling at `committed` or later needs the budget of the model of every
commitment scheme; a receipt states the local cost of an extractor or of a simulator
beside the cost of acquisition. The honest side, the clause,
the stages and the statement of each property are read from its entry in the formal library;
`CORE-LIBRARY.md` §2.9 prints what GL3 reads.*

**GL1. Form.** `goal name = property(S, name = value, …) [<= ceiling]` stands at the top level
of a module and names a scheme. A property and a model are entries of the vocabulary of kind
`property` and `model`, named through the module `zkc::security`, which has no source file;
`CORE-LIBRARY.md` lists them with what GL3 reads of each. The value of an argument is a word of
the goal (GL2), a name, a model applied to its budget (`random_oracle(queries = 2^80)`), or a
tuple of values. A role in an argument is named as in the roster of the scheme's protocol.
**Message:** "`<random_oracle>` is not a property: the properties are the entries of the
vocabulary named through `zkc::security` (…)".

**GL2. Arguments.**

| Argument | Values | When absent |
|---|---|---|
| `model` | one model or a tuple of models: `random_oracle(queries = n)`, `generic_group(operations = n)`, `algebraic_group`, a proximity regime (`johnson`) | the plain model |
| `stage` | one of the words `written`, `committed`, `constructed`, `serialized` | the last stage the scheme has |
| `statement` | `fixed`, `adaptive` | `adaptive` for a `derived` scheme, `fixed` otherwise |
| `corrupted` | online roles, where the property leaves a choice | the property's |
| `decisions` | `hidden`, `observed(n)`, for a verifier with a secret | — |
| `keys` | a key generator, where the property needs one | — |
| `clause` | the label of a `reduces`, `proves`, `knowledge` or `zero_knowledge` clause | the only clause of the kind the property needs; refused when the contract has several |
| `spec n = e` | a static term without free names, for each specification-only static parameter of the protocol instance of the scheme (SP11) | refused when the instance has such a parameter |
| `claims` | `residual` (the returned claims are part of the reduced statement, and the receipt says so), or the scheme that opens them | refused when the protocol returns claims |

The stages of a scheme: `written` always; `committed` when a `commit` line realizes a kind of its
protocol; `constructed` and `serialized` under `construction derived` and `authored`.
**Message:** "`stage` is one of written, committed, constructed, serialized; not `<final>`".

**GL3. Typing.** The vocabulary gives, for each property, its honest side, the clause it needs,
the stages at which it is stated and the constructions it admits. The scheme has the stage of
the goal; the property admits that stage and the scheme's construction. The clause exists and is
unique or named; a goal that names none of several clauses of the kind is refused. For a property whose honest side is the verifier: the deciding role of the
clause is the verifier of the scheme, and every statement argument of the clause is a function of
the scheme's statement or of pinned values; a `spec` port is admitted when the statement is
`fixed`, and under `adaptive` only when a fact available to the verifier equates it with such a
function. An `interactive` scheme that a goal names states its prover (SC3). **Messages:**
"`<Sumcheck>` has no `zero_knowledge` clause; add `zero_knowledge by … using …` to
`spec for <Sumcheck>`"; "the protocol of `<S>` returns claims; the goal says how they are
settled"; "`<S>` has no stage `committed`: it has no `commit` line; its stages are written,
constructed, serialized"; "`honest_verifier_zero_knowledge` is stated at the stages written,
committed; this goal is at `serialized`: write `stage = written`"; "`unforgeability` is not
stated of a scheme with `construction interactive`; it admits derived, authored".

*The abilities of a simulator.* The abilities are permissions. For a zero-knowledge property the
property, the construction and the stage of the goal bound what the simulator of the clause may
be given; a simulator need not use what it is allowed, and a clause that lists an ability outside
the bound is refused:

| Property, construction and stage | The simulator may be given |
|---|---|
| `honest_verifier_zero_knowledge` | `coins` |
| `zero_knowledge` of a `derived` scheme at `constructed` or `serialized` | `programming`; not `coins`: the simulated role has no coins there |
| `zero_knowledge` in every other case: at `written` or `committed`, where the verifier is interactive and may deviate | nothing in this signature, which has no argument for the verifier's strategy: the clause is `by external` |
| any property | `coins` only where the simulated role has coins; `programming` only where there is a random oracle to program: not at `written` or `committed`, and not under `construction interactive` |
| any property | `trapdoor` only when a model of the goal is a model of a reference string that names that role among the offline roles whose coins a simulator may be given. The vocabulary has no such entry yet: its form is settled when the first pairing-based argument is written, and until then a goal that uses `trapdoor` is refused |

**Messages:** "`zero_knowledge` at `constructed`: `<simulate>` is given `coins`, and a derived
verifier has no coins; a simulator there may program the oracle"; "`programming` needs a random
oracle; `<S>` at `written` has none"; "`trapdoor` gives the coins of <O>; no model of this goal
authorises it"; "`<Tested>` has two `proves` clauses; name one: `clause = <exact>`".

**GL4. Bound and ceiling.** The bound is an output of the formal library. A goal may carry a
ceiling, a `rational`. A ceiling needs every budget that its bound depends on: the budget of each
model that has one (`random_oracle(queries = …)`, `generic_group(operations = …)`); for a
property other than `completeness` of a `derived` scheme at the stage `constructed` or
`serialized`, the model `random_oracle` with its budget; and, at the stage `committed` or later,
the budget of the model of every commitment scheme that the scheme names (the queries of the
random oracle for a scheme built on a hash, the operations of the group model for one built on a
pairing). A ceiling is a request: nothing relates it to its budget before the bound is proved.
**Messages:** "a ceiling needs a budget: write `random_oracle(queries = …)`"; "a ceiling on
`<soundness>` of a `derived` scheme at the stage `<serialized>` needs a query budget: write
`model = random_oracle(queries = …)`, or state the goal at `stage = written`"; "a ceiling at
`committed` needs the budget of the model of `<Tree<Keccak256>>`: write
`model = random_oracle(queries = …)`".

**GL5. Standing.** A goal is refused at its own line and never makes the program fail to
compile. A goal without a proof is open, and the receipts check reports it. A goal whose clause
names an external statement (SX6), or states a relation bound to `external`, rests on the formal
library for what it says: the tools report it as such and never as checked. A receipt shows: the
exact statement and its domain; the local cost of the extractor or of the simulator that its
clause names (FN7), beside the cost of acquisition that the theorem of the formal library gives;
the value of each specification-only parameter; the hypotheses that contracts contribute (SX7),
with the witness
that they are satisfiable; the laws, the rows, the kernels (FN5) and the hardness assumptions it
rests on, one by one; the external statements it rests on; for a scheme with `retry`, the
payloads and stops that depend on the attempt number (SC6); the entries that compute statement
components as host code. Which hardness assumptions a receipt may rest on is project
configuration.

### 6.15 Entries

*State: layer C, carried; not frozen.*

**EN1. Host level.** An `entry def` is a function that the host calls. It is the only code that
calls `prove`, `verify` and `run` of a scheme. No `def` and no `protocol` calls an entry or runs
a scheme; in particular a protocol does not verify a proof of another scheme (recursive
verification is outside this reference). **Message:** "`<S>::verify` runs a scheme; only an
`entry def` calls it".

**EN2. Boundary.** An entry has no static parameters. Each sized type of its signature, and of
the statement and the keys of a scheme, is an admission check at the host boundary: a value that
fails it is refused before any role runs (TY14).

**EN3. Interactive runs.** A scheme is run interactively by `construction interactive` and
`S::run`; there is no entry that applies a protocol.


---

## 7. Elaboration to the core

The target is the core. §7.0 summarizes it, and §9 says what the language requires of it.

### 7.0 The core, in one page

A module of the core holds declarations and definitions; nothing in it has a name that matters:
names of definitions, roles, sites, fields and arguments are discardable annotations.

| Module-level record | Holds |
|---|---|
| `core.record` | positional field types and a use mark (copied freely, at most once, exactly once) |
| a variant declaration | the alternatives with their payload types, by position; an alternative without a payload has the empty tuple |
| `core.operation` | a row of the vocabulary: the vocabulary name, the static arguments, the function type, and the kind: pure, restricted or sampling |
| `core.oracle` | a primitive kind: its data, position and row types, sizes included, and the function of its `answer` |
| `func.func` | a structured function of the local dialect: whether it can stop, signature, custody of linear results, the name of its kernel when it has one, the specification-only mark |
| `core.def` | a protocol: role count; one port per holder of each input and output; agreements; one region ending in `core.return` |
| `core.contract` | the `spec` ports and clauses of one definition |
| `core.declaration` | a scheme: role kinds, prover, verifier, statement, construction, the functions of its suite and of its layout, the functions and keys of its commitment schemes, search, pins, step parameters |
| `core.claim` | a goal |

**Rows.** A row has one of three kinds. A *pure* row is a total function of its inputs, and it
returns no value of a type that may be empty. A *restricted* row is a function on a domain; it
names its *domain row*, a pure row with the same inputs and the one output `bool`, which decides
the domain. A *sampling* row is a law: a distribution on its one output. No row stops with a
reason that a program names. A restricted row applied outside its domain stops with the
reserved reason `undefined`, which no guard and no function names, and the check of facts
(§7.1 item 4) admits a program only when every application is inside its domain. That is the
sense in which no row stops (B6, GU1): an admitted program never stops `undefined`.

**Operations that the core owns.** The values of `bool`, of naturals, of sequences, tuples,
records and variants are fixed by the core, and so are the operations on them: the arithmetic
and the comparisons of naturals, the operations of `bool`, the length, the reading, the slicing,
the concatenation and the filling of a sequence, the refining operations `seq.sized` and
`nat.below`, the widenings, and the making and taking apart of data. They are a closed list
(§7.4). They are not rows of the vocabulary: their meaning is the core's, and no model of the
vocabulary chooses it. Seven of them have a domain (`nat.sub`, `nat.div`, `nat.rem`, `seq.at`,
`seq.slice`, `seq.sized`, `nat.below`) and stop `undefined` outside it, as a restricted row
does.

Types: `i1` (`bool`); the count type (`nat`); `fin<n>` (`index<n>`); `seq<T, n>` with `n` a
literal, and `seq<T>` whose length is a property of the value; tuples; record and variant types
by the number of their declaration; nominal types of the vocabulary, among them `nonzero<F>`,
which is a nominal type at the type `F`; the handle type of a `core.oracle` row; an opening
claim, used exactly once. No type mentions a value or a variable: in an instance every size is
a literal. A type may have no value.

| Operation of a protocol body | Does | Site |
|---|---|---|
| `core.at` | one role performs one local operation on values it holds, with the regions of that operation; a `local.guard` so performed is how that role stops | no |
| `core.exchange` | one value from a sender to a receiver | yes |
| `core.draw` | one role samples a law, one sampling row, and every receiver gets the value | yes |
| `core.sample` | one role samples a law | yes |
| `core.repeat` | participants repeat a region. The count is a number of the operation, or one copy per participant with a maximum; the operation gives each participant the iteration number; it carries values from one iteration to the next, and it collects values, which it returns as one sequence per collected value | no |
| `core.choose` | participants choose a region by a tag each holds. The tag is a condition, an arm number, or an alternative of a variant, whose region takes each participant's own copy of the payload | no |
| `core.apply` | applies a `core.def` under a role map | yes |
| `core.oracle_send` | registers data at the ideal oracle of a kind; a handle for the holders and the reader | yes |
| `core.oracle_open` | the reader's and the opener's claims are checked against the ideal oracle; consumes them | yes |
| `core.oracle_combine` | a linear combination of handles, per holder | no |
| `core.attempt_number` | the attempt number at the prover | yes |
| `core.return` | the outputs | — |

A protocol body has no guard of its own: a guard is a local operation, `local.guard`, which one
role performs in a `core.at`.

The local dialect has `local.apply` (a row), the operations that the core owns under their names
(`nat.add`, `seq.at`, …, among them `local.make`, `local.get` and `local.variant`),
`local.literal`, `local.call`, `local.if`, `local.loop`, `local.match`, `local.guard` and
`local.yield`. `local.loop` is the one loop of local code. Its count is a number of the
operation or a run-time natural; it carries values from one iteration to the next; and it
collects one value of each collected type per iteration, which it returns as a sequence. A
`for`, a comprehension and a binder form are this operation (§7.4).

A site is a number: the sites of a definition are numbered from 0 without gaps, and no two
operations share one. Which event of the source an operation belongs to, which part of that
event it is and, in a loop whose iterations are emitted in sequence, which iteration, is not in
the core: the frontend writes it in the table of sites (§7.5). An effect of a run is identified
by the path of the applications through which its definition was reached, then by its site.

### 7.1 What the frontend computes, in order

1. **Names.** Every `use`, `::` path, dot call, operator and mathematical form is resolved to a
   declaration. Modules, sections, visibility and interfaces leave no operation.
2. **Instances.** Elaboration starts at the roots (SP7). A reference `m<σ>` reached from a root
   gives one instance per declaration and values of `σ`: a `core.def`, a `func.func`, a
   `core.record`, a variant declaration or a `core.operation`. A type argument is a closed type;
   a natural argument a numeral; a module argument its declaration at its own arguments.
   `C::Value` and `R::Degree` become the type or the numeral; `C::f(x)` a call of the member's
   instance. The frontend keeps, beside each instance, the declaration and the arguments it came
   from, so that a theorem stated over an interface can be installed at its instances (§10.2).
   For a function member that is generic over a module parameter it also delivers the generic
   definition, in which an operator on a type member is the member of the interface (NL6),
   together with its instances.
3. **Roles.** The rules of §6.4 give every name its holders and every expression its computing
   roles, on the source. Each name becomes one value per holder. Every operation the frontend
   emits carries its role; no later stage computes placement.
4. **Facts.** The frontend records nothing for a fact. The guard, the condition of a choice, the
   count of a loop and the type that a fact follows from are operations and types of the
   emitted program, and the admission of the core recomputes from them, by its own calculus,
   what each role knows at every operation. It checks every application of an operation that
   has a domain: `seq.at` and `seq.slice`, natural subtraction, division and remainder, the
   refining operations `seq.sized` and `nat.below`, and a restricted row, which is justified by
   its domain row applied to the same operands and known to be `true`. A program that passes
   never stops `undefined`: no function of it, on any arguments; no protocol of it, for any
   side and whatever the other roles do; and so no role program. The calculus of the core is
   what decides: a program is accepted for its facts exactly when the admission of the core
   admits it, and TY4, TY8 and TY9 describe that calculus in terms of the source. A term of
   the source that is written twice is one value because the admission shares equal
   applications before it checks; the frontend emits every use, and holds no calculus of its
   own.
5. **Expansion.** Sends, queries and opens of derived kinds and of instances of an `oracle def`
   are replaced as §7.6 states, in dependency order. Only primitive kinds reach the core.
6. **Sites.** The sites of each definition are numbered as EV3 states. Each operation of an
   event has a site of the core, a number, and the table of sites gives its site of the
   source, its part and its iteration (§7.5).
7. **Annotations.** Names of definitions, roles, sites, fields, arguments and clauses, and source
   locations, are written as discardable attributes. No name reaches a symbol, a type or an
   identity.
8. **Identities.** The *deployment identity* of a scheme is the hash of the canonical form of a
   projection of the program: the closure of its protocol instance, which is the definitions,
   functions, records, variants, rows and oracle rows that the instance reaches through deployed
   references, numbered in the order of first reach from that instance; with it, the deployed
   members of the modules that the lines of the scheme name, and the digest of every asset that
   a reached module is bound to. It is per scheme. Specification items, goals, entries, other
   schemes, kernels, the specification-only members of a module, specification-only static
   parameters, and whatever only they reach are outside it by construction. The proof identity
   is the hash of that projection together with the declaration, which holds only what the steps
   run (§7.8), and the admitted parameters. The key of a goal is separate: it covers the
   deployment identity and the fields of the goal, with the specification items it names and the
   values of its specification-only parameters. The module identity stays the hash of the whole
   form.
9. **Rows and kernels.** Which rows and which kernels a scheme needs is stated by the
   `= primitive("…")` bindings and the `#[kernel("…")]` attributes of the closure of its protocol
   instance, by the rows of §7.4, and by nothing else. The frontend records them beside the
   module; a kernel is implementation data and is in no identity, and neither is a
   specification-only member of a module.

### 7.2 Declarations

| Source | Core |
|---|---|
| `module`, `section`, `use`, `pub`, `interface` | nothing; a `law` of an interface leaves, per implementing instance, a specification-only function and one obligation record of the module; a `law` of a module leaves the same per instance of its scope; a static name leaves nothing: it is a numeral. A sort leaves nothing: `T::m` is the type or the numeral that the vocabulary gives, `T::f(x)` a `local.apply` of the member's row |
| `type T = primitive("row", args)` | a nominal type of the vocabulary |
| `type T<…> = U` | nothing: an alias is expanded |
| `struct`, `linear struct` | `core.record`: positional field types and the use mark; field names are annotations |
| `enum` | a variant declaration |
| `def` with a body | a structured `func.func`: whether it can stop (FN2), the signature, for each linear result its custody (fresh, or the input it continues), and the name of its kernel (FN5) |
| `def … = primitive("row")`, a member `def f(x) = primitive("row")` | `core.operation`: the row at its static arguments; a call applies it |
| `module M: I = primitive("row")` | no operation; its function members are `core.operation` rows of the vocabulary, its natural members numerals |
| `module M: I = asset(name)` | no operation; its natural members are numerals, and each function member is a constant: the content of the asset decoded at the type of the member, at the digest of the asset |
| a module that implements `Kind` and not `Derived` | a `core.oracle` row per instance: its three types, with literal sizes, and the `func.func` of `answer` |
| a module that implements `Commitment`, `Suite` or `Layout` | the `func.func`s of its deployed members, per instance; a scheme that names it refers to them (§7.8). Its specification-only members are specification-only functions, recorded beside the module |
| `spec def`, `relation` with a formula | a structured `func.func` with the specification-only mark. A relation is such a function to `i1` over its statement parameters and then its witness parameters; the core has no relation definition, and the split between the two is kept by the frontend (§7.10) |
| `relation … = external("name")`, `spec def … = external("name")`, `spec type … = external("name")` | an opaque header; the external name is carried in the table of names, beside the module, and in no operation |
| `protocol` | `core.def`: role count; one port per holder of each port and result; an agreement for every port and result with several holders; the specification-only mark for `spec protocol`; one region that ends in `core.return` |
| `spec p: T` port | an entry of the `spec` ports of the protocol's `core.contract`; `core.def` has no port for it |
| a port marked `private` | the declaration lists the input as private: it is no statement component and is not absorbed |
| `oracle def` | no operation; its instances are expanded (§7.6) |
| a module that implements `Derived` | its `Send` and `Open` are `core.def`s |

### 7.3 Types

| Source | Core |
|---|---|
| `bool`, `nat` | `i1`; the count type |
| `index<s>`, `byte` | `fin<n>` with `n` the value of `s`; `fin<256>` |
| `nonzero<F>` | a nominal type of the vocabulary: `nonzero` at the type `F` |
| `[T; s]` | `seq<T, n>`, `n` the value of `s` |
| `[T]` | `seq<T>`; its writing, reading and absorbing rows carry the length |
| tuples, records, variants | a tuple; the number of the `core.record`; the number of the variant declaration |
| `Oracle<K>`, `K` primitive | the handle type of the `core.oracle` row |
| `Oracle<F<…>>`, an instance of an `oracle def` | a tuple of the parent handles and the captures |
| `Pending<K>` | an opening claim, used exactly once |
| `rational` | none: it occurs in specification-only functions |
| a fact (TY4) | none: nothing is recorded for a fact; the admission of the core recomputes it (§7.1 item 4) |

### 7.4 Local code

| Source | Local dialect |
|---|---|
| an operator on a type of a sort (a field, a ring, a group) or on `nonzero<F>`; a call of a `def` bound to a row | `local.apply` of the row |
| an operator on naturals or on `bool` | the operation that the core owns (`nat.add`, `bool.not`, …) |
| an operator or a mathematical form on a declared type; a call of a `def` with a body | `local.call` |
| number and byte-string literals | `local.literal`. A number checked against a type of sort `Ring` is a literal of that nominal type, whose value the type of the vocabulary gives: `from_nat` of the number (TY6). It applies no row |
| `[a, b]`, a tuple, `T{…}`, `{r with f = v}`, `.f`, `.0`, a pattern | `local.make`; `local.get`; a pattern on a linear record consumes it |
| `xs[i]`, `xs[a..b]`, `xs ++ ys`, `[v; n]`, `length(xs)` | the operations `seq.at`, `seq.slice`, `seq.concat`, `seq.fill`, `seq.length` of the core; `seq.at` and `seq.slice` are applied on their domain |
| `xs + ys`, `xs - ys`, `xs * a`, `xs == ys` on collections of elements of a sort | `local.apply` of the rows `seq.add`, `seq.sub`, `seq.scale`, `seq.equal` |
| `a - b`, `a / b`, `a % b` on naturals | the operations `nat.sub`, `nat.div`, `nat.rem` of the core, applied on their domain |
| `guard c else ρ` | the condition, then `local.guard` with `ρ`. A guard never elaborates to a row and changes no type. Where a conversion by a fact stands (TY5), the frontend applies the refining operation on the value at that place: `seq.sized` or `nat.below`, operations of the core, or the restricted row `field.nonzero`. The guard or the condition that made the fact is what justifies it; the comparison of a field element with `0` is emitted as the domain row `field.is_nonzero`, so that it justifies `field.nonzero` |
| a widening (TY5) | `seq.unsized`, `fin.to_nat` and `fin.widen`, operations of the core; the pure row `field.from_nonzero`; for the elements of a collection or the components of a tuple, the collection or the tuple made again from the converted components |
| `if c: … else: …`, `if c then a else b` | `local.if`; a fact of the condition justifies a refining operation in the arm, at the conversion that needs it, as for a guard |
| an `if` with a static condition (TY9) | the operations of the arm taken; no `local.if` |
| `a and b`, `a or b` | `bool.and`, `bool.or` when neither operand can stop; otherwise `local.if`, whose other region returns the literal `false` (for `or`, `true`) |
| `match`, `Enum::Name(e)` | `local.match`, each region over the payload of its alternative; `local.variant` |
| `for i in a..b`, uniform or with a run-time count; `for x in xs` | `local.loop`: the count is a number of the operation for a static range or a sized collection, and a run-time natural otherwise; the index is the iteration number plus the start of the range; the updated `mut` names are the carried values |
| `for i in a..b`, stepped, or with an index that is static in the body | the iterations in sequence, each with the index a literal (§7.5) |
| `[e for x in D]`, `[e for x in D if c]` | a `local.loop` that collects `e`: with a static count and a sized result over a static range or a sized collection, with a run-time count and an unsized result over a run-time range or an unsized collection; with `if c`, a loop that carries an unsized sequence and appends under the condition. A comprehension typed per element is a `local.make` of its elements |
| a binder form | on elements of a sort, the row of the form (`seq.sum`, `seq.product`, `seq.inner`) applied to the collected sequence; on naturals and on `bool`, a `local.loop` that carries the accumulator; on a declared type, a `local.loop` that carries the accumulator over `add` from `zero()` (`mul` from `one()`) |
| `for … collect (ys = e)` | the collected values of the `local.loop` for a uniform loop; a `local.make` of the per-iteration values for a stepped one |
| `mut`, `:=` | carried values and region results; nothing at run time |
| the expression of an expression body, `return e` | `local.yield` |

The body of a `for`, of a comprehension and of a binder form is the region of its `local.loop`.
It is no function of the module and has no name: it is identified by its place in its
definition.

**The rows that the frontend applies.** These rows of the vocabulary have no declaration in
source: an operator, a literal, a form or a statement of the language applies them. They are
normative. Their meaning in the formal library is a function; for a collection row, the fold of
the element row.

| Family | Rows | Applied by | Count |
|---|---|---|---|
| field | `field.add`, `field.sub`, `field.mul`, `field.neg`, `field.inverse`, `field.pow`, `field.equal` | `+ - *`, prefix `-`, `/` by a `nonzero`, `^`, `==` | 7 |
| `nonzero<F>` | `field.nonzero`, a restricted row with the domain row `field.is_nonzero`; `field.is_nonzero`; `field.from_nonzero` | a conversion by a fact (TY5); the comparison of a field element with `0`; the widening of `nonzero<F>` to `F` (TY5) | 3 |
| ring | `ring.mul`, `ring.pow` | `*` and `^` by a natural on a type of sort `Ring` that is not a field; its `+`, `-` and `==` are the rows of the group family | 2 |
| group | `group.zero`, `group.add`, `group.sub`, `group.neg`, `group.scale`, `group.equal` | the literal `0`, `+ -`, prefix `-`, `x * a`, `==` | 6 |
| collection | `seq.add`, `seq.sub`, `seq.scale`, `seq.sum`, `seq.product`, `seq.inner`, `seq.equal` | element-wise `+ -` and `* scalar`, `∑`, `∏`, `⟪ ⟫`, `==`, on collections of elements of a sort | 7 |
| sampling | `law.uniform`, at a type that is a law (TY15): `bool`, an `index<n>`, a field, `nonzero<F>`, a group, and a tuple or a sized collection of laws, for which it is one row at the composite type | `draw`, `sample` | 1 |

Twenty-six rows. Each is pure, except `field.nonzero`, which is restricted, and `law.uniform`,
which is sampling. A number literal of a field or of a ring is no row: it is a `local.literal`
of the nominal type. The rows `field.mul`, `field.neg` and `field.pow` are also applied at the
type `nonzero<F>`, for `*`, prefix `-` and `^` on operands of that type (TY6), and
`field.inverse` takes and gives a `nonzero<F>`. `seq.inner` on points and scalars is the
multi-scalar multiplication; its kernel is the fast algorithm. Besides them the frontend applies
the function members of the sorts, which `zkc::algebra` declares without a body
(`group.generator`, `field.from_nat`, `field.to_nat`, `field.components`,
`field.from_components`, `field.embed`, `field.coefficients`, `field.from_coefficients`,
`field.root`), and the rows that a declaration of the core library binds: the eight rows of
`zkc::oracle`, the hashes and the extendable-output functions of `zkc::hash`, `group.to_bytes`
and `group.from_bytes` (`CORE-LIBRARY.md`). Every other row is bound by a declaration of a
library. The row `field.embed` has a result range, a power of B3 that its signature in source
cannot write: applied to a `nonzero<Base>` it gives a `nonzero<Self>`.

**The operations that the core owns.** They have no declaration in source either, and they are
not rows: the core fixes their meaning (§7.0).

| Family | Operations | Domain | Applied by | Count |
|---|---|---|---|---|
| natural | `nat.add`, `nat.sub`, `nat.mul`, `nat.div`, `nat.rem`, `nat.pow`, `nat.equal`, `nat.less` | `nat.sub` on `b <= a`; `nat.div` and `nat.rem` on `1 <= b` | `+ - * / % ^`, `==`, `< <= > >=` | 8 |
| `bool` | `bool.and`, `bool.or`, `bool.not`, `bool.equal` | — | `and`, `or` (when no operand can stop), `not`, `==` | 4 |
| sequence | `seq.at`, `seq.slice`, `seq.concat`, `seq.fill`, `seq.length` | `seq.at` on a position below the length; `seq.slice` on `a <= b`, `b` at most the length and, into a sized result, `b - a` equal to its size | `xs[i]`, `xs[a..b]`, `++`, `[v; n]`, `length` | 5 |
| refining | `seq.sized`, `nat.below` | the length equal to the size; the number below the bound | a conversion by a fact (TY5) | 2 |
| widening | `seq.unsized`, `fin.to_nat`, `fin.widen` | — | the widenings of TY5: `[T; s]` to `[T]`, `index<s>` to `nat`, `index<s>` to `index<t>` | 3 |
| data | `local.make`, `local.get`, `local.variant` | — | sequence literals, tuples, records, fields, positions and patterns, alternatives | 3 |

Twenty-five operations. One that has a domain is applied only where the facts of the role that
computes put its operands in the domain (TY5, TY7, TY8), and the admission of the core checks
the application again (§7.1 item 4). `seq.length` is the operation that `zkc::prelude` binds as
`length`: that binding names an operation of the core as another names a row (NL9).

### 7.5 Protocol bodies

**Operations of a role.** A `core.at` holds one local operation that one role performs, with
the regions of that operation: the arms of a `local.if`, the body of a `local.loop`. Each
statement that computes gives, for each of its computing roles in roster order, the sequence of
that role's `core.at` operations for the whole expression, in the order of HO4 (rows,
operations of the core, literals, `local.call`, `local.if`, comprehensions). The cutting of
expressions into operations is thereby determined; `core.local_call` is not produced. A copy of
a binding that cannot stop and that its role never uses is removed; a copy that can stop is
never removed. Inside a `core.choose` or a `core.repeat` only the participants have operations:
a closed binding is computed there by the participants, and no copy is made at another role
(HO2). Beside the operations of each statement and role the frontend writes their *stop
summary*: the operations among them that can stop, in order, with their reasons.

| Source | Core |
|---|---|
| `x = e`, computed by `S` | for each role of `S`: that role's `core.at` operations for `e` |
| `x @S′ = e` | the same, for the roles of `S′` |
| `guard @Q c else ρ` | for each role of `Q`: that role's `core.at` operations for the condition, then its `local.guard` with `ρ`, in a `core.at` of its own. A guard is a local operation that a role performs: the protocol body has no guard of its own. A refining operation is applied among the `core.at` operations of the statement whose conversion needs the fact |
| `y <- send e from p to R` | the `core.at` operations of `p` for `e`; one `core.exchange` per receiver, in the order written, each a part of the event with a site of its own (EV3); `y` is the sender's copy and the receivers' results |
| `c <- draw L from d to R` | `core.draw`: role `d`, receivers `R`, the sampling row of the law at its type, which is one row also for a tuple or a sized collection of laws; one site |
| `s @p <- sample L` | `core.sample`: role `p`, the law's row, one site |
| `k @p <- attempt` | `core.attempt_number`: role `p`, one site |
| `y <- C<σ>(args) @(…)`, `C<σ>(args) @(…)` | the `core.at` operations of each role for the arguments it computes; `core.apply`: the callee's instance, the total role map with one entry per callee role, one site; one operand per holder of each port. A `spec` argument is typed against its port and is not part of the emitted package: the frontend keeps it with the table of sites (the site of the application, the port, the expression) for the layer that elaborates contracts (§7.10) |
| `for`, uniform or with a run-time count | `core.repeat`: the participants; the count, which is a number of the operation for a static range or a sized collection, and otherwise one copy per participant with the bound of CT4 as its maximum; the iteration number, which the operation gives each participant and to which that role adds the start of the range for the index; the carried values: each updated `mut` name per holder; the collected values per holder, which the operation returns as sequences, sized for a static count; the captures |
| `for`, stepped, or with an index that is static in the body | the iterations in sequence, each elaborated with the index as a literal; see below |
| `if` | `core.choose` on a condition: the participants; the condition per participant; two regions, that of `false` first; the holders of the updated `mut` names as `output_holders` |
| `if` with a static condition (TY9) | the statements of the arm taken, in place: no `core.choose` and no participants. The sites of the arm not taken keep their numbers and have no operation at the instance |
| `match` | `core.choose` on the alternatives of the variant: the matched value per participant; one region per alternative, in order, which takes each participant's own copy of the payload of its alternative, with its type. The participants of a side agree on the alternative; their payloads are not compared. No projection of another alternative exists in an arm |
| `return (e…)` | the `core.at` operations of each role for what it returns; `core.return` with one output per holder of each result |
| `#[site(n)]`, a binder, a loop index | annotations |

**Stepped loops.** A static loop that is stepped (TY10), and a static loop whose index is static
in its body, is its iterations in sequence: each iteration is elaborated with the index as a
literal, so it is closed code with literal sizes, and the core needs no operation for it. A
collected name is a `local.make` of the per-iteration values at each holder: a `seq<U, n>` when
they have one type, the tuple otherwise (TY16). A stepped `for` of a function is the same in
its region. The emitted code is linear in the count. Measured on `Sumcheck<n>` of
`programs/sumcheck.zkc` for `n` from 0 to 20: about 50 operations and 2.8 KB of package per
round, and typing, emission, admission and projection together under 13 ms at `n = 20`. One
repetition over an unsized carrier, with the length at each boundary as a fact indexed by the
iteration, would make the code independent of the count and would add to the core a fact about
a carried value; the core does not have it.

**Sites.** A site of the core is a number of its definition, and no two operations share one
(§7.0). The frontend numbers the events of a definition as EV3 states, and gives each part of
each event, and each occurrence of it in a loop whose iterations are in sequence, a site of the
core of its own. Beside the module it writes the *table of sites*: for each site of the core,
the site of the source with its name, the part, the iteration of each loop in sequence around
it, and the place in the source. A reference `sites.x` (EV4) is resolved through the table. An
occurrence in a run is the path of the applications through which the definition was reached,
then the site of the core; in a `core.repeat`, the iteration is given by the meaning of the
operation.

### 7.6 Oracles

*State: layer D, carried; superseded, pending the redesign of derived kinds (the claims of a deferred
query, the expansion of `open` on a derived kind, the commitment of an input handle of a derived
kind).*

Nothing is tested at an oracle send or at a query: the shape is in the types.

| Source | Core |
|---|---|
| `h <- send e to r as oracle<K>`, `K` primitive | a `core.at` region of the sender for `e`; `core.oracle_send`: the data, the sender, the reader, the holders (the roles of `C`), the `core.oracle` row of `K`, one site |
| the same, `K` derived | `core.apply` of `K::Send`; the handle is the record of what it returns, and the holders keep the data |
| `(rows, c) <- query h from o at ps deferred`, `K` primitive | a `core.at` region of `o` that applies `K::answer` to the data and every position; one `core.exchange` of the rows for the whole block from `o` to the reader (part `rows`); a `local.make` of the claim at each of the two |
| `rows <- query h at ps` | the same, then `core.oracle_open` of the claim (part `opening`), under the same site |
| `pending(h, p, v)`, `h at p == v` | a `local.make` of the claim at the opener and at the reader |
| `open c₁, …, cₙ` | for each claim of a derived kind, in the order written, `core.apply` of the kind's `Open` on the block of its claims (part `reduce k`); its residual claims take the place of the claim in the block; then exactly one `core.oracle_open` over the primitive claims of the block, in order (part `opening`). The commit step of the tool splits it by commitment scheme and names the parts |
| `query v at ps`, `v` an instance of an `oracle def` | one block over the tuple of its parents: the positions of all occurrences of each parent in the row expression, in the order of first occurrence; one exchange of the parents' rows; both roles compute the rows of `v` by a generated function. A deferred query yields the tuple of the parents' claims. No row of `v` is sent |
| `open v at p == x`, `v` an instance | that query, and a `local.guard` of `row == x` performed by the reader, with reason `reject` |
| `F(h…, c…)` | per role that forms it, a `local.make` of the tuple of the parent handles and the captures |
| `h₁ + h₂ * c` | `core.oracle_combine`, per holder |
| `data(h)`, `lower(h)` | pure rows in a `core.at` region; for an instance of an `oracle def`, the generated tabulation |
| `commit K with S(…)`, `commit sites.x with S(…)` | the commitment schemes of `core.declaration`: per `core.oracle` row and per site, the instance of `S` with every static argument resolved (the functions `commit`, `opening` and `check` that the commit step applies) and the sites of its keys |

### 7.7 Specification and requests

*State: layer B, carried.*

| Source | Core |
|---|---|
| `spec for P:` | one `core.contract`: the definition, its `spec` ports, the bindings of `spec` arguments, the clauses |
| `requires`, `ensures`, `invariant … at i` | a clause with its kind and a specification-only function for the expression; arguments are an agreement, a port, a `spec` port or a carried name; `invariant` has the position of the loop |
| `reduces @D R to S`, `proves @D R` | a clause with the deciding role and the relation and arguments of each side; `proves` has the constant `true` as its `to` side; each `through` is an entry with the position of its loop |
| `knowledge R′(a…) by e or Q(b…) by f` | a clause with the relation and its statement arguments, the extractor, and, when written, the alternative relation with its arguments and function; with `by external("name")`, the external name in place of the functions |
| `zero_knowledge by s using π` | a clause with the simulator, its abilities and the role whose view it produces |
| `charge sites.x <= e` | a clause with the site, as a path of site numbers, and a specification-only function for `e` |
| `law` | per implementing instance (for a law of a module: per instance of its scope), a specification-only function and an obligation record of the module; the record says whether the build decided a closed law by evaluation (SP10) |
| `goal n = property(S, …) <= c` | one `core.claim`: the declaration, the property row, the position of the clause, the model rows with their arguments, the stage, adaptivity, corrupted roles, decisions, keys, how returned claims are settled, the values of the specification-only parameters, the ceiling. Its key is the hash of these fields with the deployment identity and the specification items it names |

### 7.8 Schemes

*State: layer C, carried. The declaration holds only what the steps run.*

`scheme S = P<σ>:` becomes one `core.declaration`. The frontend writes every field; nothing is
derived below it.

| Field | From |
|---|---|
| protocol | the instance `P<σ>` |
| kind of every role | `offline` and `ideal` lines; online otherwise |
| prover, verifier | SC3: computed, or the line `prover P` |
| statement | SC4, in order, with the commitment of every input handle; private inputs listed apart |
| construction, suite | the `construction` line; the suite is an instance of a module, and the field refers to the functions of its deployed members |
| stages | `written`; `committed` when a kind is realized; `constructed`, `serialized` under `derived` and `authored` |
| commitment schemes and keys | the `commit` lines: per kind and per site, the instance of the scheme's module with every static argument resolved; a key is a site |
| pins | the `pin` lines, or the proposal file |
| search | `grind`, `retry`, `samples derived by` |
| layout | the instance of the layout module, with the `carry` and `recover` entries; `zkc::layout::canonical` when absent |
| rows | those of the closure of the protocol instance (§7.1 item 9). Kernels and specification-only members are no field of the declaration: they are recorded beside the module |
| dependencies on the attempt number | SC6 |

The declaration has one kind and no acceptance. The decision of the verifier is that its program
returns.

### 7.9 Entries

*State: layer C, carried.*

An `entry def` becomes a structured function and a host entry of the interface that the frontend
writes beside the module: its name, its signature, the schemas of its records, and the admission
checks of EN2. A call of `S::prove`, `S::verify` or `S::run` is a call of the host function that
the compiler generates for the scheme; the host function of a verifier returns the verifier's
results and stops with `reject`. An entry is not a definition of the `core` dialect and is in no
identity of a proof.

### 7.10 What the frontend keeps for the later layers

This is a contract of the elaboration, not surface. The later layers (the specification, the
steps of a scheme, oracles) cannot reconstruct the following, so the frontend records it:

| Kept | For |
|---|---|
| for every instance: the generic declaration, its static arguments and the members selected | a law or a theorem is installed at the actual specialization, not at a matching name (item 2 of §7.1, SP12) |
| the identity of each value, and the evidence that each holder has for it. A value of the core has one holder; the evidence is no record of its own: it is the guards, the conditions, the counts and the types of the emitted program, from which the check of facts recomputes what each holder knows (§7.1 item 4) | a copy or a send does not carry the facts of another role (TY4, TY14) |
| for every event: its application path, its static site and its occurrence (the iteration, the attempt). The table of sites (§7.5) holds, for each site of the core, the site of the source, the part and the iteration of each loop in sequence around it | a site alone does not tell repeated or nested executions apart (EV3, EV4) |
| for every `spec` argument of an application: the site of the application, the port and the expression, with the table of sites | the argument is typed and is not in the emitted package; its binding in the contract of the caller is layer B's to complete (SX4, §7.7) |
| for every relation: which of its parameters are statement parameters and which are witness parameters | the package holds a relation as a specification-only function to `i1` (§7.2), and the clauses read the split (SX3, SX6) |
| whether an event is of the source or generated by a step of the tool | openings, generated coins and the actions of the Fiat–Shamir step belong to the view of a later stage |
| the actual operands, results and outcomes of calls | a law of a callee and a security result stay bound to what was applied, on the paths that stop as well |

The record of a run is a typed view per stage. The relation between the views of two consecutive
stages is kept by the step that produces one from the other. `P::Run` and `P::Received` are the
views of the written protocol (§8); a scheme has views at its later stages, so a simulated view
at `committed` contains the digests and the openings. A claim keeps its handle, its position and
its row through every regrouping.

---

## 8. Generated members

A protocol, a scheme and a layout module have members that no declaration writes. They are named
through `::` (NL3 c). A role of the roster of `P` stands as the static argument of `Inputs`,
`Coins` and `Received`, and nowhere else as a static argument. A field of a generated record is
identified by its site, not by the site's name: the name is the selector an author writes, and a
site without a name has the field `site<n>`, `n` its number (EV3). A site of an arm that a
static condition does not take has no field in any generated record at that instance (TY9).

*State: the members of a protocol are layer B, those of a scheme and of a layout module layer C;
carried. A field of `Run` for a site in a loop has the type of its
`collect`; `Runs` is not defined for a draw in a choice, a field of `Run` for an event in a
choice is an `Option`, and the order of the tree is stated; `S::Witness` carries the data
and the commitment state of input handles; the field leaf of a layout is over `F: Field`.
The record of a run is a typed view per stage (§7.10): `P::Run` and `P::Received` are the
views of the written protocol, and a scheme has views at its later stages, so that a simulated
view at `committed` contains the digests and the openings; the members that name those later
views are not designed. Pending: `P::Received` and `P::Coins` are to include the
record of an application, and the witness the blinding of each input handle.*

| Member | Definition |
|---|---|
| `P::Run` | a record with one field for every `send`, `draw`, oracle send, `query` and application of `P`, in the order of the sites. The field holds: for a `send` or a `draw`, the value sent or drawn; for an oracle send, the data as the ideal oracle holds it, a `K::Data`; for a `query`, deferred or not, the rows read; for an application, the callee's `Run`. For a site in a loop it has exactly the type that a `collect` of the value has (TY16): `[T; n]` when the iterations share one type, the tuple of the values otherwise, `[T]` for a run-time count, the empty collection after no iteration. For an event in an arm of a choice it holds an `Option` of the value, `None` in a run that takes another arm. A `sample` and an `attempt` have no field in `Run`: they are coins |
| `P::Runs<k₁, …, kₘ>` | defined when no `draw` of `P` is in a loop, in a choice or inside an application. One natural per `draw` of `P`, by position, in the order of the sites: the accepting runs of a tree that agree before the `i`-th draw and take `kᵢ` different values at it; a `[P::Run; k₁ * … * kₘ]` in the lexicographic order of the tree, the first draw most significant: the run that takes the `j₁`-th value at the first draw, …, the `jₘ`-th at the last stands at the position `(…(j₁ * k₂ + j₂) * k₃ + …) * kₘ + jₘ`. Each `kᵢ` is at least 1 and at most the number of values of the law drawn at site `i`; the naturals are all 1 (one run, which an extractor that does not rewind reads) or all at least 2 (SX6) |
| `P::Inputs<R>` | a record of the ports that role `R` holds, by name; handles and `spec` ports excepted |
| `P::Coins<R>` | a record of the draws and samples of `R`, by site: the values |
| `P::Received<R>` | a record of what `R` receives: the sends and draws to `R`, and the rows of the queries that `R` reads, by site. The data of an oracle is not received |
| `S::Statement` | a record with one field per statement component, in order (SC4); for an input handle, its commitment |
| `S::Witness` | a record of the prover's inputs that are not in the statement and, for each input handle whose data the prover holds, of its data and of the state that its commitment returned |
| `S::Keys` | a record of the values at pinned sites that the verifier receives |
| `S::Proof` | the proof; a sealed type |
| `S::Results` | a record of the results that the verifier holds |
| `S::prove(statement, witness) -> S::Proof` | runs the prover; can stop |
| `S::verify(keys, statement, proof) -> S::Results` | runs the verifier; stops with `reject` when it rejects; returns `()` when there is no result |
| `S::run(port = value, …) -> S::Results` | under `construction interactive`: runs every role in one process; stops when a role stops |
| `L::write<T>(value: T) -> [L::Unit]` | for a module `L` that implements `Layout`: the writer of the type `T`, generated from the leaves of `L` as TY14 states; `T` is inferred from the value |
| `L::read<T>(units: [L::Unit]) -> Option<(T, nat)>` | the reader of `T`: the value and the number of units it took, or `None`; `T` is written |
| `==` on a record or a variant whose home module declares no `equal` | the conjunction of `==` on the fields; on a variant, the same alternative and equal payloads (TY12) |

So a `knowledge` clause can name what was committed inside a run: for
`codeword <- send values to V as oracle<table<F, 2^k>>`, the field `runs[0].codeword` is the
table, a `[F; 2^k]`, and the soundness of "commit, then check" is stated on the protocol that does
both (`programs/spot_check.zkc`). Such a clause reads one run, and the bound it claims is the sum of the
charges of the contract (SX6). **Messages:** "`<X>::Runs` is not defined: the draw `<c>` (line <n>) is
inside a loop; the tree of runs of an extractor over a loop of challenges is not expressible yet:
state the clause as `knowledge R(a…) by external("name")`"; "`<X>::Runs` is not defined: the draw
`<c>` (line <n>) is inside a choice"; "`<X>::Runs` takes one natural per
draw of `<X>` (1)"; "the naturals of `<X>::Runs` are positional: one per draw of `<X>`, in the
order of its sites"; "`<runs[0]>` is a `<X::Run>` and has no field `<committed>`";
"`<Oracle<table<F, 8>>>` is not written: a layout writes naturals, field and group elements, and
tuples, records, variants and collections of them".


---

## E. Constraint systems

*State: layer E; a design of the standard library, not frozen. Nothing in it is a rule of the
language and no language item is added.*

**What a constraint system is.** A constraint system is written in source, as a module that
implements an interface of `zkc::constraint` whose one function member is generic over an algebra
over the trace field. `zkc::constraint` is standard library (§2.5): no rule of this reference
reads a name of it, and the compiler sees nothing in a constraint system as one written thing.
Four things come from that one function: the relation of the specification, the verifier's check
at opened values, the prover's quotient, and the numbers that a protocol needs.

```zkc
// zkc::constraint::algebra
pub interface Algebra<F: Field>:
    type T
    def constant(c: F) -> T
    def add(a: T, b: T) -> T
    def sub(a: T, b: T) -> T
    def mul(a: T, b: T) -> T
pub module Over<F: Field>: Algebra<F>                      // T = F
pub module Lifted<E: ExtensionField>: Algebra<E::Base>     // T = E
pub module Degrees<F: Field>: Algebra<F>                   // T = a degree

// zkc::constraint::air
pub interface Air<F: TwoAdicField> where (2 <= Degree):
    nat Width
    nat Public
    nat Constraints
    nat Degree
    def constraints<X: Algebra<F>>(
        local: [X::T; Width], next: [X::T; Width], public: [X::T; Public],
        first: X::T, last: X::T, transition: X::T
    ) -> [X::T; Constraints]
    law degree(): …                                             // closed: decided by evaluation

// zkc::constraint::air::table<F: TwoAdicField, A: Air<F>>
pub relation Satisfied<h: nat>(public: [F; A::Public]; trace: [[F; A::Width]; 2^h])
pub def identity<E: ExtensionField, h: nat>(…) -> bool      // the verifier's check
pub def quotient<E: ExtensionField, h: nat, n: nat>(…)      // the prover's quotient
```

The operators of `Algebra` are its members (NL6), and `Algebra` has no law `natural`; the
parameters elided with `…` are not given here.

`Algebra` is a signature without ring laws, and an implementing module is an interpretation of
that signature. `Over` and `Lifted` are rings; `Degrees` is not one (its subtraction is a
maximum) and is not of the sort `Ring`. What connects the interpretations is not a law of the
interface but typing: in `constraints` the type member `X::T` is opaque (SP12), so the body uses
its carrier only through `constant`, `add`, `sub` and `mul`, and a constraint that tests a value
for equality or branches on it is refused. The formal library then proves once, for all such
bodies, that interpretations related by a relation which the members preserve give related
results. Two uses: with homomorphisms, every evaluation agrees with the polynomial meaning; with
the relation "the degree of the polynomial is at most the degree value", the degree
interpretation is a sound upper bound. The degree enters the error of the identity test, so the
soundness of the table argument rests on it.

| System | Form in source |
|---|---|
| an AIR | a module that implements `Air<F>`; with challenges, `StagedAir<F>` |
| R1CS, a customizable constraint system | data: `R1cs<F>` and `Ccs<F>` have naturals and matrices as members; a conversion is a module (`FromR1cs<F, S>: Ccs<F>`) |
| a Plonkish system | `Plonkish<F>`: a gate function over an algebra, with data (selectors, copies) |
| a layered circuit | data |
| an imported system | data bound with `asset` (NL9), `module M: Graph<F> = asset(name)`, and an interpreter in source, `Interpreted<F, M>: Air<F>`; the relation it denotes is `Satisfied` over the interpreter |

**What the design uses of the frozen layer.** A function member generic over a module parameter,
with operators on a type member (NL6) that is opaque in the body (SP12); a closed law decided by
evaluation, which is how the
stated degree of a system is checked (SP10, FN7); a `where` on a law and on a relation (SP4,
SP10, SX3); a `law` of a module (SP10); `asset` as naturals and data (NL9); and the frontend
delivers the generic definition together with its instances (§7.1 item 2). These rules are
frozen; the interfaces above are not.

**Other parts of the design.** A promise pair is two labelled clauses (SX7). An index is a static
argument or an input handle (SC4). The mixed-field additions: `field.embed` takes a `nonzero` to
a `nonzero` (§7.4); the model of a type that is both an extension and two-adic states that its
roots are the embedded roots of its base; `zkc::coset` and `zkc::polynomial` gain the lifts to an
extension; `fri` is generic over the field of its domain. The back end compiles the body of a
constraint function, and there is no hand-written kernel for it; kernels stay for what does not
depend on the system (interpolation, batch inversion, the tree, the closed forms of selectors).

**Open.** The theorem of the formal library that SP12 prepares, and its two uses, are not
written. The form in which the back end holds a lowered constraint function and the data of an imported system.
Tables with several components, buses, periodic and preprocessed columns; the second stage of a
lookup. The layer closes when a STARK is written.

---

## 9. What the language requires of the core

The core language that §7 elaborates into is specified with the compiler
([the core language](../docs/spec/core/README.md)). The forms of layer A elaborate into it as
it stands: sized types and facts, the three kinds of rows, the operations that the core owns,
guards as local operations, choices over a condition, an arm number or a variant, loops with
their collected values, and sites as numbers with their names in a side table.

The forms of the later layers need what the core does not have yet: requests to an oracle and
their claims, the attempt number of a retry, the contracts and claims of the specification
layer, and the layouts and suites written in source. They are designed with those layers, and
a program that uses one of them waits for it.

---

## 10. Open points

### 10.1 Choices of this reference

*State: a record, carried. Where a choice and the rule it names differ, the rule holds: so for
choices 2 (the sorts and sixteen other items), 3 (the prelude re-exports the sorts, seven with
`Ring`), 4 (the field leaf of a layout is over `Field`), 8, 9 to 11, 12, 13, 15 and 20 (a static
name also stands in a module and in a section); in 25, form (A) for stepped loops is decided
(§7.5).*

Where the criteria left two rules that cannot both hold, a form without a production, a
signature without a body, or a program that could not be written, this reference makes the
smallest choice that keeps the document set consistent.

| # | Choice | Where |
|---|---|---|
| 1 | An interface is a sort when it is `Group` or its `where` requires `Self` to be of a sort | SP3 |
| 2 | Twenty language items: `Option`, `PrimeField` and `ExtensionField` are named by rules, besides seventeen others | §2.4 |
| 3 | The six sorts are in the prelude as a closed table of the language | NL4, §2.5 |
| 4 | `canonical` is a module in source; the leaves of a layout are a natural below `2^64`, an element of a prime field and a group element; an element of an extension field is written as its coefficients | TY14, `CORE-LIBRARY.md` |
| 5 | `L::write<T>` and `L::read<T>` are generated members of a layout module | §8 |
| 6 | The condition of an `if` gives its facts to its arms | TY9 |
| 7 | A fact may be about an arithmetic expression over immutable names, identified by its text; `t - u <= t` | TY4 |
| 8 | Collected values without a common type are a tuple, and a tuple is indexed by a static natural | TY16, TY7 |
| 9 | `knowledge R(a…) by e [or Q(b…) [by f]]`, with the relation applied to its statement arguments; `by external("name")` in the clause | SX6, §5.12 |
| 10 | The signature of a simulator: inputs, coins exactly with `coins`, the offline role's coins exactly with `trapdoor`, at most one parameter of randomness, a law; with `programming` it returns the coins | SX6 |
| 11 | `P::Runs` is not defined for a draw in a loop or inside an application; its naturals are positional | §8 |
| 12 | Default instances: a type at a type of the vocabulary of its sorts, a module at an implementing module of the program; beyond three naturals, the diagonals and each natural varied alone | SP7 |
| 13 | `Commitment` has `Proof<n>` and the member `opening`; the static arguments of a scheme that a `commit` line leaves out are solved from the kind, by matching module applications | SC5, SP6 |
| 14 | A function member of an interface may have a `where`; an interface without members has no suite; a `spec def` member may be bound to `external` | §5.11, SP4 |
| 15 | The stages of a scheme; a ceiling on a `derived` scheme after its construction needs the random-oracle budget | GL2, GL4 |
| 16 | A goal that states an external relation is reported like one whose clause is external | GL5 |
| 17 | A verifier that checks nothing is a report, and an undeferred query counts as a check | SC8 |
| 18 | A literal that is not a multiple of the characteristic is a `nonzero<F>` | TY6 |
| 19 | A `rational` context is given by the expected type | TY8 |
| 20 | A static name is a binding without `mut` and without a type whose right side is a size | TY2 |
| 21 | Every `use` names something; a module does not declare a name of the prelude | NL3, NL10 |
| 22 | A library under `zkc::` binds only rows of the printed vocabulary; a row of a project is reported | NL9 |
| 23 | A kernel may stand on a member definition; a function that can stop has none | FN5 |
| 24 | The forms without a production have their own messages, and their words are not reserved | GR6 |
| 25 | Carried: a loop writes no maximum and no type for its state; `for … collect`; arithmetic on naturals never stops; `nat` is a run-time type; numerals among natural arguments are written by name; a brace import binds the listed names; a local name is bound once; `@D` on `reduces` and `proves`; `Self`; the argument `claims` of a goal; a type is not bound to an asset; an oracle without a `commit` line stays ideal under `interactive`; the formatter keeps `prover P` and type annotations; a `def` without `->` returns `()`; a closed expression that can stop acts; `query h from o at ps`; a loop of zero iterations types nothing; `==` is `equal` when declared; form (A) for stepped loops; a list may end with `,` | — |

### 10.2 Left open

| # | Point | What would settle it |
|---|---|---|
| 1 | **How a stepped loop is represented below the surface**: (A) the iterations in sequence, or (B) one repetition over an unsized carrier with a length invariant | closed: the iterations in sequence, each occurrence of a site a site of its own (§7.5). Measured on `Sumcheck<n>` for `n` up to 20: about 50 operations and 2.8 KB of package per round, and typing, emission, admission and projection under 13 ms at `n = 20`. Form (B) is not part of the core; the size and the checking time of proof terms over a stepped loop are not measured |
| 2 | **Variants and shared `match`** are in the language and not validated | the programs `programs/sigma_or.zkc`, `programs/request_dispatch.zkc` and `programs/variants_example.zkc` elaborated and their endpoint meaning checked; a variant with a claim as payload |
| 3 | **The tree of runs of an extractor over a loop of challenges.** `P::Runs` is not defined for a draw in a loop, there is no recursion, and the clause takes an external statement | a type for a tree whose depth is the count of a loop, and a way to write the extractor over it |
| 4 | **Oracles whose shape is a run-time value**, and sizes over run-time naturals | a library that needs them; they can be added without invalidating programs written under static shapes |
| 5 | **Handles of one family and different shapes**: polynomials of different degrees do not combine; the collected handles of a folding loop are a tuple | no widening (OR8); a named conversion of a library, examined with the commitment schemes that must realize it |
| 6 | Collected values and fields of `Run` of different types | closed: a tuple; nothing joins to a collection of unsized collections |
| 7 | The signatures of `Suite` and `Layout` are proposed and not validated; the schedule of the Fiat–Shamir step is not a rule yet | a byte-exact reproduction of a deployed transcript: the EIP-4844 challenge, one Merlin transcript, ML-DSA's |
| 8 | Whether a commitment whose opening is interactive is always a derived kind over a non-interactive one | a second case besides FRI |
| 9 | How a theorem over an interface and its laws is reused when the core holds only instances; laws are typed at instances only | a design on the Lean side; §7.1 item 2 keeps the association |
| 10 | Default instances beyond 0 to 3 and a bound that a `where` states | a library that states the instances at which it is to be checked |
| 11 | A static parameter that only the specification uses | closed: `spec n: nat`, given by the goal (SP11); how an application gives it is item 24 |
| 12 | How the table of mathematical forms grows; the element-wise product is the first candidate | by writing libraries |
| 13 | How the equation of a kernel and its body is tested at every build, and where a receipt lists it | the first back end with kernels |
| 14 | One clause that names the artifact a property asks for, in place of `knowledge` and `zero_knowledge` | a third such family of properties |
| 15 | A multiplicative sort | a group of the vocabulary whose operation is the multiplication of a ring that programs also use |
| 16 | Extension fields as one row with static arguments; the lattice library; four collection operations that no source names | the Lean side; the owners of those libraries. Decided: a ring is a sort, and a quotient ring of polynomials is a row with static arguments |
| 17 | The type `Residual` of a derived kind and the batching of several claims by its `Open`; hiding commitments and zero knowledge of oracle protocols | the redesign of derived kinds and of `Commitment`: FRI as a derived kind with a batched opening; the masked inner-product protocol over Pedersen |
| 18 | Private-coin and designated-verifier protocols; `private` on a send; multi-receiver sends against a sender that does not follow the protocol; handles with several readers; recursive verification | the first library that needs each |
| 19 | The legacy `construction` blocks and transcript code: their successor is a source suite and a layout | the libraries that use them |
| 20 | The formatter is specified and not implemented; block comments and string escapes are unexamined | — |
| 21 | The order of validation | decided: a Lean frontend on layer A, Schnorr and Sumcheck end to end |
| 22 | The theorem that related interpretations of an interface give related results, for the definitions that the opaque typing admits (SP12) | written in the formal library over the local dialect, with its two uses for constraints |
| 23 | An error in an arm of a static `if` that no checked instance takes is found late (TY9) | the implementation |
| 24 | How a protocol that applies another gives the callee's specification-only static parameter its value | closed: a specification argument, `C<…, spec e = term>(…)` (SP11) |
| 25 | The budget of the build for closed laws; whether a row over a collection counts once or once per element; the manifest of assets; the form of the model of a reference string that authorises a `trapdoor` (SP10, FN7, NL9, GL3) | settled with the layers that use them: constraint systems, the first receipt that states a cost, the first pairing-based argument |
| 26 | The form in which the back end holds a lowered constraint function and the data of an imported system | a `constraint` dialect of the back end is the candidate |
| 27 | Indexers as roles | the pairing-based arguments |
| 28 | **The length of a slice as a fact** (TY7). The length of a slice of an unsized collection, of a concatenation and of a filled collection is not made a fact about the name that the value is bound to, because the check of facts of the core has no rule that gives it from the parts: `t = a[0..length(a) - 1]` followed by a slice of `t` is refused by TY8. No program and no test of this reference needs it | a rule of the check of facts for the length of a slice, of a concatenation and of a filled sequence, and with it the fact in TY4, which gives a bound name the other facts of its right side |
| 29 | The readers of `zkc::layout::canonical` form their value in a `mut` accumulator: `read_natural` is refused by TY8 once the law of `Layout` is typed at `canonical` | the readers written with `∑`, with layer C |
| 30 | `CORE-LIBRARY.md` §1.2 gives each suite of the catalogue three members, and `Suite` declares more | the rows of the catalogue suites, with layer C |
| 31 | `programs/support/fibonacci.zkc` is the withdrawn form of a module bound to an asset, and `programs/stark_example.zkc` depends on it | the programs of layer E, rewritten with their layer |
| 32 | The test `M-SUMX3` of layer C names a module by its full path without a `use`, which NL3 does not admit | the test, corrected with layer C |
| 33 | The frozen test `T-P6` cites SX3 for a `;` in the arguments of a call of a function, and FN6 states that refusal | the test accepts both rules: `refuse FN6 SX3` |
| 34 | **A profile of layer A.** The whole-program tests of layer A (`M-SUM…`, `M-GKR…`, `M-FRA…`, `M-IPA…`, `M-SCH…`) carry declarations of later layers and generated members, and no rule says what an implementation of layer A does with them. Until one does, an implementation of layer A *types* the declarations of layer A (types, records, variants, functions, interfaces and implementing modules, laws, `spec def`s and the formulas of relations, protocols with their events of layer A and the `spec` arguments of their applications), from the roots of SP7 and, in a test, from the instances that a line `// instantiate:` names; it *parses and resolves the names of* the items of later layers and types nothing in them (`spec for` and its clauses, the lines of a `scheme` other than the protocol instance it names, `goal`, `entry def`, `oracle def`); and it *leaves* a root that reaches a form it does not elaborate, and says which: an oracle event or a handle placement (layer D), a generated member of §8 (layers B and C), and `attempt` (EV7), which is of layer A and is not elaborated yet | a rule beside the table of §0.1: which declarations are typed, which later items are parsed and resolved only, which generated signatures a test may assume, and how roots are given |
| 35 | The catalogue gives no generator for `field.root` at the quartic extension of KoalaBear and at the scalar field of BLS12-381 | the vocabulary states the generators |

### 10.3 Where the criteria did not survive being applied

*State: a record, carried.*

1. **A short list of items.** The test for an item (a rule mentions the name) gives twenty: the readers
   of a layout and the decoders of a suite return `Option`, and the generated writer of a field
   element distinguishes a prime field from an extension.
2. **The prelude and the sorts.** "Nothing enters the prelude because it is frequent" and a
   prelude with six sorts, four of which no table mentions: the sorts are read as a closed table.
3. **`canonical` as a row and layouts as source.** The item is a module in source.
4. **The leaves of `Layout`.** `write_field<F: Field>` cannot be written in source, where no
   declaration dispatches on a sort; the leaf is a prime field and an extension is structure.
5. **Static shapes with collections of handles and with handle arithmetic** (the layers of a
   folding argument; polynomials of different degrees).
6. **No partial row, and decoders that return `Option`**, with facts made only by guards: a
   function that must not stop could not read a collection of run-time length at all.
7. **The signatures of extractors and simulators** are given by no criterion where a clause must
   give them: the alternative of a `knowledge` clause, the abilities, the randomness.
8. **"Each natural at 0, 1, 2 and 3"** says nothing of types and modules and multiplies.
9. **A law for a uniform group element** exists and is not derived by any suite: under
   `derived` it is refused.
10. **A kernel on a body that cannot stop**, with guards whose test is the costly part.
11. **`position<n>` of `Suite`** needs `1 <= n`, which no member could state.
12. **"A verifier that performs no guard and no `open`"**: an undeferred query is its check.


---

## 11. Checks run on this document

The library of `lib/`, the worked programs of `programs/` and the tests of `conformance/` are
checked by the test suite of the frontend (`lean/frontend`), which reports for each test whether
its outcome is the expected one, and for each worked program how far it is compiled.

---

## Appendix A. Rule identifiers and messages of the tools

Every code of a rule that refuses, with the number of wordings of its message that were
counted when the rules were written; the messages quoted in §3, §5, §6 and §8 are among those
wordings. `GR` without a
number is a token that no production admits ("expected `:`, found `->`").

The table does not count the rules `SP11`, `SP12`, `FN7` and `SX10`, nor the messages that this
document gives in NL6, NL9, SP4, SP8, SP10, TY2, TY6, TY13, RM3, FN5, SX6, SC5, GL3 and GL4 beyond
those wordings. The message of a range whose start exceeds
its end is CT6's.

| Codes | |
|---|---|
| lexer (§3.1) | LX1 (2), LX2 (1), LX3 (2), LX4 (3), LX5 (1), LX6 (5), LX7 (3), LX8 (2), LX9 (1), LX10 (1) |
| parser (§5.0) | GR (3), GR1 (3), GR2 (2), GR3 (2) |
| names (§6.1, §2.4) | NL1 (2), NL2 (8), NL3 (8), NL4 (1), NL5 (2), NL6 (12), NL7 (3), NL9 (5), NL10 (2) |
| static parameters (§6.2) | SP3 (9), SP4 (5), SP5 (9), SP6 (3), SP7 (1), SP8 (9), SP9 (1), SP10 (1) |
| types, sizes, facts (§6.3) | TY1 (7), TY2 (6), TY4 (1), TY5 (9), TY6 (4), TY7 (10), TY8 (4), TY10 (2), TY11 (4), TY12 (8), TY13 (25), TY15 (1), TY16 (1) |
| holders (§6.4) | HO1 (4), HO2 (2), HO3 (6), HO5 (4) |
| events and sites (§6.5) | EV1 (5), EV2 (2), EV3 (4), EV4 (3), EV5 (3), EV6 (1) |
| guards (§6.6) | GU2 (2), GU3 (1) |
| control (§6.7) | CT1 (3), CT2 (1), CT4 (2), CT5 (5), CT6 (2) |
| role maps (§6.8) | RM1 (5) |
| linearity (§6.9) | LN1 (1), LN2 (6), LN3 (1) |
| oracles (§6.10) | OR2 (11), OR3 (5), OR4 (7), OR5 (3), OR6 (5), OR8 (3), OR9 (8), OR10 (2) |
| functions (§6.11) | FN1 (5), FN3 (6), FN4 (1), FN5 (3), FN6 (14) |
| specification (§6.12, §8) | SX2 (3), SX3 (5), SX4 (4), SX5 (2), SX6 (30), SX8 (2), SX9 (12) |
| schemes (§6.13) | SC1 (2), SC2 (4), SC3 (10), SC4 (2), SC5 (30), SC6 (4) |
| goals (§6.14) | GL1 (2), GL2 (7), GL3 (9), GL4 (2) |
| entries (§6.15) | EN1 (2) |

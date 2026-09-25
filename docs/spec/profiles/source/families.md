# Invocation-selected protocol families

A family separates a finite stored template from the configuration and inputs
selected for an actual invocation. A configuration can contain dimensions,
layouts, enabled components and schema selections. It is not limited to a round
count. Its bound inputs have a dependent type `Inputs config`.

## Actual selection

Selection has the complete execution interface:

```text
ingress : RawInput → State → Execution State Event (Σ c : Config, Inputs c)
member  : (c : Config) → Inputs c → Proc Σ Result
```

Execution runs ingress, then the returned member on its actual residual state,
retaining its event prefix. A stopped ingress runs no member. This rule covers
hostile raw inputs independently of an honest producer's encoder image. A pure
parser is a specialization with explicit failure and no extra effects.

An admissible family specifies valid configurations and bound inputs. Each
selected member has conformance, return-phase and all-reply bound obligations;
the bound may depend on the configuration. The `Selects` ingress law quantifies
over every raw input and initial state in the claimed domain: each actually
returned configuration and inputs satisfy the
allowed-input predicate. Together with member admission, it discharges the
selected member's obligations at its contract's declared initial phase.
Type-correct ingress alone
does not establish validity or justify moving later guards to entry.
Hostile-input coverage extends only over that domain. Restricting it to an
honest encoder's image does not cover arbitrary accepted input; exclusions need
an enforced transport or invocation precondition.

Member admission names a logical initial phase. It does not certify ingress or
show that ingress leaves the member at that phase. If `phaseOf` interprets the
actual residual state's interaction phase, successful ingress also supplies
`contract(config, inputs).initialPhase = phaseOf(ingress(raw, state).state)`
before admission is used at that entry. The realization justifies `phaseOf`
against its handler's phase transitions. An effectful ingress can select allowed
inputs yet violate this equation. Its own effects, progress and any required
conformance need separate evidence. Input handles must also denote live values
in that residual state; input validity alone does not establish this. A
compiler-facing adapter retains the ordinary stored-source elaboration and
binding obligations. The member's call bound does not bound ingress work.

`SelectsReady` states a residual-state postcondition for every successful ingress
in the claimed domain. Its predicate may combine allowed inputs, the phase
equation, live resources and their representations. `Selects` is its
state-independent specialization. `Admitted.selected_ready` uses such a
domain-wide proof to obtain member admission at the actual entry phase, retaining
the readiness facts; it does not prove those facts automatically.

Ingress may itself be a stored finite process. `run_proc` identifies its
execution followed by member selection with ordinary `Proc.bind`. Existing
conformance, return and all-reply bound composition laws then apply to the whole
invocation. A uniform invocation bound additionally bounds ingress and every
member reachable by any typed ingress reply; configuration-wise finite bounds
alone do not supply it.

An old fixed program embeds using effect-free constant ingress. Its complete
execution is unchanged. Introducing a parser, extra event, stricter decoder or
different guard order is not that embedding and requires its own correspondence.

## Compact counted templates

The [common grammar](common-protocols.md) is parameterized by a count type.
`Nat` gives resolved programs; scoped [public dimensions](public-dimensions.md)
give counted templates. `mapCounts` changes only counts, including counts inside
stored callees. It preserves operands, schemas, sites, bindings and structure.
Identity and composition hold; structural node count is unchanged.

Instantiation evaluates each expression in the selected dimension environment.
Substitution followed by instantiation equals instantiation in the substituted
environment. Literal expressions recover the old resolved program exactly.
Instantiation commutes with both scheduled-participant and open-role projection.
The resolved projection/execution theorems therefore continue to apply to each
instance; this alone is not a theorem about a symbolic native runner.
The stored definition table shares one dimension scope: a call supplies no
dimension arguments of its own. Per-call substitution is a different stored
grammar with its own binding and projection laws.

The counted grammar does not vary port types, schema choices or component
topology within one template. A structured family may select among checked
templates. A compact compiler representation for broader variation supplies its
own formation, instantiation and projection law; a host function is not that
representation.

## Role knowledge

Each role must determine its required behavior from its permitted local view
on admitted worlds. A constructive selector `select` satisfies
`select (view world) = required world`. Consequently two admitted worlds with
the same local view require the same selected behavior. The role need not learn
configuration components irrelevant to its behavior.

The required behavior need not be the literal projected syntax. An uninvolved
role may erase a counted inert computation under an applicable preservation law,
so different source counts need not require different local choices. Such erasure
must retain every required observation, residual-state relation and admission
condition; equality of one returned value alone does not justify it.

Giving every role a common parameter does not prove that it received or may
observe that parameter. Honest send/decode coherence and coverage of all accepted
raw inputs are separate requirements. A later challenge that selects different
receive schemas needs explicit delivery, justified merging, or a proved
state-preserving segment boundary. Calling it another entry supplies none of
those laws. Existing open-role alignment remains distinct from distributed
cancellation or equality of all terminal outcomes.

## Compiler obligations

One compact native template must correspond, at each admitted configuration, to
the resolved member used by admission. A native implementation checks arithmetic
and allocation capacity independently of semantic call counts. A construction
must bind the selected configuration, inputs, source closure and runtime operands.

Availability analysis may conservatively accumulate possible dependencies.
Resource authority needs exact provenance: a loop swapping two capabilities
depends on count parity, and a union of their possible origins does not authorize
either. Symbolic analysis can use invariants, expressions, checked case splits,
or refuse. Zero iterations and counts beyond machine capacity remain explicit.

A serialized count field denotes a `Nat` instance. A carrier whose counts stay
symbolic at run time is a different carrier with its own admission and execution
contract.

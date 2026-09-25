# Disclosure of artifacts and execution

A disclosure claim compares the complete information released to a selected
recipient across specified worlds. Internal execution refinement supplies such
a claim only when its relation and observation cover that recipient's actual
information.

## Allowed worlds and selected release

Let `W` be a world type, `allowed : W → W → Prop` the world pairs compared by
the policy, and `release : W → O` a deterministic release. Define:

```text
Permitted(allowed,release) :=
  ∀ w v, allowed(w,v) → release(w) = release(v).
```

The allowed relation can restrict the comparison to worlds with the same
public inputs or an explicitly approved disclosed value. It need not be an
equivalence relation or compare every pair. Its adequacy to the intended
secrecy claim is a separate policy obligation: an empty relation makes
`Permitted` vacuous.

For an explicitly approved value `approved : W → A`, deliberate release uses:

```text
allowedApproved(w,v) := allowed(w,v) ∧ approved(w)=approved(v).
```

`approved` is permitted under `allowedApproved`. This equation describes the
chosen weakening of the secrecy comparison; it does not approve an arbitrary
new disclosure. Recording a value in a log does not change the policy.

The release function includes all recipient-visible channels claimed by the
experiment. Artifacts can expose source selection, generated code, specialized
captures, proofs and certificates, receipts, digests and diagnostics. Runtime
observations can expose return and stop status, events and retained state.
Which of these are visible is an explicit experiment operand.

## Deterministic joint release

For `artifact : W → A` and `runtime : W → R`, define:

```text
publish(w) = (artifact(w), runtime(w)).
```

For the same allowed relation:

```text
Permitted(allowed,publish) ↔
  Permitted(allowed,artifact) ∧ Permitted(allowed,runtime).
```

Equality in both coordinates gives equality of the pair; projecting equality
of the pair gives each coordinate. Erasing runtime events is insufficient
when the artifact itself varies across worlds that must be compared.

## Randomized joint release

For `release : W → PMF O`, exact randomized permission is:

```text
RandomPermitted(allowed,release) :=
  ∀ w v, allowed(w,v) → release(w) = release(v).
```

Each world supplies its actual [normalized law](probability.md#normalized-discrete-distributions).
If `p(w) : PMF X` describes its execution samples and `observe(w) : X → O`
the complete release, then `release(w) = map(observe(w),p(w))`.

For artifact/runtime release the observation type is the whole pair `A × R`.
Its two coordinate distributions are marginals of this one joint law. Equality
of those marginals across worlds does not in general imply equality of the
joint law. Composing independent channels from their marginals requires their
actual within-world joint laws to be products in both worlds.

*Example (informative).* Let `r` be a uniform bit and let secret `s` be fixed.
Release artifact `r` and runtime bit `s xor r`. Each channel alone is uniform
for either secret. Their pair reveals `s` by xor, so joint permission fails.

## Couplings and joint agreement

Let `p : PMF X` and `q : PMF Y` be the sample laws in two compared worlds.
A coupling is a joint law `j : PMF (X × Y)` with actual marginals:

```text
map(first,j) = p
map(second,j) = q.
```

For observations `f : X → O` and `g : Y → O`, the support condition

```text
∀ (x,y) ∈ support(j), f(x)=g(y)
```

implies `map(f,p)=map(g,q)`. Only supported sample pairs need agree. The
equation follows by substituting the two marginal laws and composing their
observation maps.

For artifact functions `a : X → A`, `a' : Y → A`, and runtime functions
`r : X → R`, `r' : Y → R`, it is sufficient that, on the support of the
same `j`:

```text
a(x)=a'(y) ∧ r(x)=r'(y).
```

Two separate couplings can satisfy the individual coordinate equalities and
still be incompatible. The pair requires one coupling satisfying both.
Pointwise equality using the identical random seed is sufficient when the
actual laws support it, but is not required; a coupling may relate different
private seeds.

A bijection of sample spaces preserving an observation establishes a
correspondence between observation fibers. It gives equal probabilities only
when it also carries the actual sampling law to the other law. Uniform finite
sampling is one such case; a bijection alone supplies no sampling premise.

## Postprocessing and continuation

For a fixed deterministic `project : O → A`, permission of `release` implies
permission of `project ∘ release`. In the randomized case it implies permission
of `w ↦ map(project,release(w))`. The same argument applies to a fixed
normalized postprocessing kernel `k : O → PMF A` by substituting equal release
laws in `bind`.

“Fixed” concerns the compared world pair. A continuation that additionally
reads private state, inspects an unretained artifact or interacts through
world-dependent providers is not solely postprocessing the released value.
It must receive only the covered information or establish a stronger
state/context relation and continuation law. Sampling its randomness through
a world-dependent correlation also needs that actual joint law, not merely
equal randomness marginals.

Statistical or computational hiding selects its comparison, recipient and
resource/advantage bound in a corresponding
[experiment](experiments.md#simulation-and-extraction-claim-boundaries).
Neither hashing nor an exact deterministic projection theorem alone supplies
that experiment connection. Exact equality of the same observed ensembles
also satisfies comparisons that admit equality, such as statistical distance
zero. It does not supply a missing simulation or native-observation connection.

## Authorized-service status projection

The [authorized continuation](../profiles/services/accepted-continuations.md#ledger-receipt-and-export-result)
can retain a private receipt with the actual verifier outcome and a separate
combined execution. Its optional public projection has type:

```text
Option (Outcome Bool) × Outcome Unit.
```

Using `Terminal A = accepted(a) | rejected` from
[terminal decisions](relations.md#terminal-decisions-and-contracts), define:

```text
decision(returned(accepted a)) = returned true
decision(returned rejected)   = returned false
decision(stopped why)         = stopped why

eraseValue(returned b)        = returned ()
eraseValue(stopped why)       = stopped why

publicStatus(out) =
  (map(r ↦ decision(r.report.verifier.outcome), out.receipt),
   eraseValue(out.combined.outcome)).
```

Here `map` on the first coordinate is the option map: `none` stays `none`,
and `some r` maps its contained value. This projection erases capture and
returned payload values, events, runtime state and ledger from the release.
It still exposes receipt presence, the verifier's decision or stop reason,
and the combined return/stop status. A failed arm can therefore coexist with
a reported positive verifier decision.

Use of this projection needs permission to disclose all of those statuses
in the actual experiment. Receipt authenticity and policy-authorized export
to a selected consumer do not imply public release permission.

## Cost and implementation observations

A protocol observer can erase charge events while a performance observer
retains them. Equality under the first is not equality under the second, nor
a comparison across secret worlds. If the recipient can inspect cache accesses,
lengths, timing or addresses, the claimed release includes those channels
or establishes the applicable representation/observation law for them.

A cost claim fixes units, the work included, initial conditions, comparison
scope and evidence kind. Symbolic work, operation or byte counts and measured
elapsed time are different quantities. The
[preparation profile](../profiles/compiler/factor-preparation.md#immutable-preparation-and-prices)
selects its own exact work and price model. It does not establish native
timing or cache privacy. Comparing two upper bounds alone does not compare
actual costs; the [cost judgment](../verification/judgments.md#caller-requirements)
requires the stated relation between actual values and evidence.

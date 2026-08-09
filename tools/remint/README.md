# remint — re-minting the corpus after an identity change

Change anything the canonical preimage covers — a field, a registry entry, a
domain tag — and roughly a hundred values in the fixture corpus become wrong at
once: artifact ids, claim anchors, request citations, challenge values, proof
bytes, judgment digests. None of them are assertions. They are *fixture-internal
consistency*, and keeping them consistent by hand is a transcription task
carried out a hundred times.

```bash
python3 tools/remint/remint.py run          # re-mint the derived values
python3 tools/remint/remint.py sentinels    # what the anchors say
python3 tools/remint/remint.py status       # what is failing, and what is derivable
```

## How it derives, rather than guesses

Every refusal in this repository that rejects a cited value prints the value it
computed beside it. Those messages are an API: the tool runs the suite, reads
the refusals through a declared table of grammars, applies each
computed-for-cited pair across the repository, and repeats until nothing moves.
Files that one implementation owns outright — the execution vectors — are
regenerated from that implementation instead of patched.

A failure the table cannot parse is printed under *failures no channel
explains*. It is never skipped: a re-mint that quietly leaves something stale is
worse than one that stops.

## The two rules

**Anchors are not auto-minted.** `sentinels.json` enumerates the values that
exist to catch the one failure the parity suite is blind to — both
implementations changing the same way. Cross-implementation diffing proves the
two legs agree; it cannot notice they now agree on something else. A tool that
reset those values with everything else would be disarming the alarm it just
tripped, so `run` reports them and stops there. You review, then:

```bash
python3 tools/remint/remint.py sentinels --accept
```

`test/Meta/identity-anchors.test` runs the same check in the suite, so an
unaccepted anchor is a failing test rather than a note someone missed.

**Nothing is minted from one leg.** Anchors are recomputed through the native
implementation and the reference twin. Disagreement exits 2 and mints nothing —
a split means the change under way broke parity, which is the finding, not an
obstacle to re-minting past. (Anchors whose second leg lives in a named suite
test, or which genuinely have no second implementation, say so in their entry;
the taxonomy is at the top of `sentinels.json`.)

## What it is not for

Mutation fixtures that spell out a digest — `sed '0,/sha256:<value>/s//sha256:9999…/'`
— look like re-mint burden and are not. The literal is the same string as the
value it targets, so the sweep maintains it for free, and it is doing work no
field pattern does: selecting *which* occurrence to corrupt. Replacing one with
a pattern that names only the field silently retargets the mutation at the first
match, and the negative test then proves a different negative. Leave them
literal.

## Extending the channel table

When a new refusal starts carrying a computed/cited pair, add a `Channel` with
its grammar and which capture group is which. Prefer teaching the refusal to
print both values over teaching the tool to infer one: the error message is
read by people during a debugging session far more often than by this script.

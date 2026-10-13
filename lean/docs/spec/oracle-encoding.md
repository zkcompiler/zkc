# Encoded cached oracles

`ZkcSecurity.Oracle.Encoding` defines an independent interpretation of typed
oracle keys through an encoding. It uses the optional security package's VCVio
cache and query semantics. It does not select a native transcript provider.

Let `encode : Key → EncodedKey` be a fixed function, independent of the oracle's
answer table. A cache maps keys to optional answers. Its typed view is

```text
view encode cache key = cache (encode key).
```

The encoded handler first looks up `encode key`. On a hit it returns the cached
answer without invoking the underlying draw. On a miss it invokes the draw,
stores that answer at `encode key`, and returns the updated cache. Neither a
uniform sampling law nor independence is implicit in the word “draw”.

## State-preserving correspondence

An injective encoding satisfies the cache-update law:

```text
view encode (cache.update (encode key) answer)
  = (view encode cache).update key answer.
```

A decoder satisfying `decode (encode key) = some key` for every key is sufficient
to establish this injectivity. The decoder law says nothing about byte strings
outside the image, canonical rejection, or the native parser.

For any lawful execution monad, any initial encoded cache, and any adaptive
typed oracle program, `adaptive_projection` equates:

1. execution with encoded keys, followed by projection of the final cache; and
2. execution with typed keys and a draw obtained by composing `draw` with
   `encode`, starting from the projected initial cache.

The result and the entire projected residual cache agree. An empty encoded
cache projects to an empty typed cache. The law also applies to a program
sequenced with another typed oracle program, so the cache is shared across
those computations rather than reset between them.

An update at an encoded key outside the image leaves the typed cache view
unchanged. This is a deterministic state fact. It does not, by itself, justify
independence of answers, discard the cost of that query, or translate an
adversary that can query the full encoded-key domain.

## Applicability

The admitted client interface consists of typed keys passed through this fixed
encoder. An experiment granting arbitrary byte-domain oracle access needs a
separate adversary and distribution adapter, including queries outside the
image and their costs. An encoding that depends on sampled previous challenges
needs a different argument unless those challenges are explicitly part of the
typed key.

The implementation retains arbitrary initial caches, including entries outside
the image. The executable controls exercise adaptive repeated queries, fresh
draw counts, retained entries, and a colliding encoding that changes another
typed key's cache entry. The declaration audit checks the transitive proof
assumptions. These laws establish neither concrete hash security nor a
Fiat–Shamir security bound by themselves.

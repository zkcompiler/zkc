# Pricing alignment — zkc's FRI rows against p3-security at the pin

Where the two accountings agree, where they deliberately diverge, and
where zkc scopes out. p3-security lives at the pinned revision's
security/ crate; zkc's rows live in registry/soundness-signature.json
and price through zkc-derive with exact rationals and an obligations
ledger.

Agreements:
- The proven linear commit-term family (BCHKS 2025/2055) is the same
  formula family as p3's `commit_phase_error_ldr`; zkc's
  johnson_linear row carries it in exact dyadics with at most a
  factor-4 conservative up-rounding against p3's f64.
- Both cross-check against Ethereum's soundcalc; zkc's independent
  re-derivation is test/Soundness/soundcalc.test.
- The conjectured query pricing cites the same corrected conjecture
  (Diamond-Gruen 2025/2010 §1.5) that p3's `conjectured_error`
  implements; zkc's random_words row gates its eta_bar at or above the
  correction rather than computing it in floats.

Deliberate divergences:
- p3 optimizes the proximity parameter m per instance (up to 1000);
  zkc prices at declared parameters gated by deciders — a derivation
  is a judgment about a declared analysis point, not a search.
- p3's proven-UDR evaluates at soundcalc's theta = (1-rho)/2 point,
  which sits outside BCHKS Cor 1.4's stated window by O(1/n); zkc's
  udr row refuses that point rather than price beyond the statement.
- p3 min-composes into float bits capped by collision resistance; zkc
  never aggregates in the kernel — the witness carries exact per-round
  rationals, aggregation is the --headline display, and the sponge
  idealization is a ledger entry rather than a hash-bits cap.
- p3 composes ALI/DEEP terms around the LDT; zkc's FRI rows price the
  LDT reduction alone — protocol composition is other rows' business.
- zkc prices the above-Johnson zone through the threshold_halving row
  (ePrint 2026/858), which p3 does not carry; the row's ledger entry
  names the citation's unvetted standing, and a refutation flips its
  status the way the capacity family's was flipped.

Scoped out, with the boundary named:
- Per-site commit-pow attribution: at the pinned configuration the
  commit-pow sites are zero-bit sponge no-ops — not transcript events
  — so zkc's transcript model rightly carries nothing for them. A
  nonzero commit-pow family needs schema and multi-round scaling
  machinery first; until then the single grinding row prices the one
  pow round the transcript actually has.
- Arity above 2: the value-faithful template folds in pairs, matching
  the deployed Plonky3 defaults; p3's (folding-1) scaling generalizes
  a shape zkc does not yet seal.

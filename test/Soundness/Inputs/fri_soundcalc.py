"""The independent soundness calculator.

The cited theorems' formulas, re-implemented from the papers over exact
fractions and checked against the bounds the shipped signature declares.
Nothing here reads the kernel, the evaluator, or any C++ output: the signature
is read as data and its bound expressions are evaluated by this file's own
arithmetic. That is the point. Two implementations of the same reading can
share a misreading; a second reading of the source cannot be talked into one.

This is not the kernel's semantics and does not claim to be. It reproduces
enough of the exact-quantity grammar to evaluate a declared bound at a fixture
point, so that a formula transcribed from a paper can be compared against the
formula the signature actually declares.
"""

import json
import sys
from fractions import Fraction as F

failures = []


def check(name, got, want):
    if got != want:
        failures.append(f"{name}: theorem gives {got}, the signature declares {want}")


# --- the declared-bound reader -------------------------------------------
#
# A bound is a polynomial in the conclusion's adversary resources over exact
# rationals. Only one resource ever appears in the v0 inventory, so a sparse
# map from exponent to coefficient is enough.


class Poly:
    """Sum of coefficient * variable**exponent, exact."""

    def __init__(self, terms=None):
        self.terms = {e: c for e, c in (terms or {0: F(0)}).items() if c}

    @staticmethod
    def constant(value):
        return Poly({0: F(value)})

    @staticmethod
    def variable():
        return Poly({1: F(1)})

    def is_constant(self):
        return all(e == 0 for e in self.terms)

    def value(self):
        if not self.is_constant():
            raise ValueError("the expression is not resource-free")
        return self.terms.get(0, F(0))

    def coefficient(self, exponent):
        return self.terms.get(exponent, F(0))

    def __add__(self, other):
        terms = dict(self.terms)
        for e, c in other.terms.items():
            terms[e] = terms.get(e, F(0)) + c
        return Poly(terms)

    def __sub__(self, other):
        return self + Poly({e: -c for e, c in other.terms.items()})

    def __mul__(self, other):
        terms = {}
        for e1, c1 in self.terms.items():
            for e2, c2 in other.terms.items():
                terms[e1 + e2] = terms.get(e1 + e2, F(0)) + c1 * c2
        return Poly(terms)

    def __truediv__(self, other):
        return self * Poly.constant(1 / other.value())

    def __pow__(self, exponent):
        result = Poly.constant(1)
        for _ in range(exponent):
            result = result * self
        return result

    def __repr__(self):
        return " + ".join(f"{c}*t^{e}" for e, c in sorted(self.terms.items()))


def ceil_int(value):
    return -((-value.numerator) // value.denominator)


def quantity(node, parameters):
    """Evaluate one exact-quantity node at a fixture point."""
    kind = node["kind"]
    if kind == "rational_literal":
        return Poly.constant(F(node["literal"]))
    if kind == "parameter":
        return Poly.constant(F(parameters[node["name"]]))
    if kind == "resource_variable":
        return Poly.variable()
    operands = [quantity(o, parameters) for o in node.get("operands", [])]
    # Addition and multiplication are n-ary here; reading only the first two
    # operands would silently drop a term.
    if kind == "add":
        total = operands[0]
        for operand in operands[1:]:
            total = total + operand
        return total
    if kind == "mul":
        product = operands[0]
        for operand in operands[1:]:
            product = product * operand
        return product
    if kind == "sub":
        return operands[0] - operands[1]
    if kind == "div":
        return operands[0] / operands[1]
    if kind == "pow":
        return operands[0] ** int(operands[1].value())
    if kind == "pow2":
        return Poly.constant(F(2) ** int(operands[0].value()))
    if kind == "pow2_up":
        # The half-integer dyadic bounded above by the next power of two;
        # rounding a loss UP is the only safe direction.
        return Poly.constant(F(2) ** ceil_int(operands[0].value()))
    raise ValueError(f"the calculator does not evaluate quantity kind '{kind}'")


def bound(node, parameters):
    kind = node["kind"]
    if kind == "quantity":
        return quantity(node["quantity"], parameters)
    if kind == "add":
        total = Poly.constant(0)
        for operand in node["operands"]:
            total = total + bound(operand, parameters)
        return total
    if kind == "scale":
        return quantity(node["scale"], parameters) * bound(
            node["operands"][0], parameters
        )
    raise ValueError(f"the calculator does not evaluate bound kind '{kind}'")


signature = json.load(open(sys.argv[1]))
RULES = signature["rules"]


def declared_round(rule_id, case_name, parameters):
    """The bound the signature declares for one round case of an entry rule."""
    cases = RULES[rule_id]["body"]["rounds"]["cases"]
    for case in cases:
        if case["case_name"] == case_name:
            return bound(case["bound"], parameters).value()
    raise KeyError(f"{rule_id} declares no '{case_name}' round")


def declared_parameters(rule_id):
    return {p["name"] for p in RULES[rule_id]["parameters"]}


# --- conjectured capacity (ethSTARK v1.2 Conjecture; Block-Tiwari
# 2024/1161 Conj 1): eps = max(1/|F|, rho^ell), rho = 2^-(n-k).
#
# The rule is declared rather than admitted: the conjecture family is refuted
# as stated. It is still checked here, because a record nobody can check is
# not a record.
TOY_FIELD = 2305843009213697249


def conjectured(field_order, n, k, ell):
    return max(F(1, field_order), F(1, 2 ** (n - k)) ** ell)


for label, (n, k, ell) in {
    "capacity k=1": (10, 1, 2),
    "capacity k=2": (10, 2, 2),
    "capacity k=3": (10, 3, 2),
}.items():
    point = {"field_order": TOY_FIELD, "n": n, "k": k, "ell": ell,
             "log_blowup": n - k, "log_final_poly_len": 0}
    declared = max(
        declared_round("zkc.rbr.fri.capacity", "fold", point),
        declared_round("zkc.rbr.fri.capacity", "query", point),
    )
    check(label, conjectured(TOY_FIELD, n, k, ell), declared)

# --- grinding (ethSTARK v1.2 Thm 6): the grinded round's error scales by
# 2^-z. The rule scales a selected round of its premise, so the theorem's
# statement is the scale itself.
grinding_scale = quantity(
    RULES["zkc.rbr.grinding"]["body"]["scale"], {"z": 16}
).value()
check("grinding scale at z=16", F(1, 2**16), grinding_scale)
check(
    "grinding applied to the k=1 query round",
    conjectured(TOY_FIELD, 10, 1, 2) * F(1, 2**16),
    declared_round("zkc.rbr.fri.capacity", "query",
                   {"field_order": TOY_FIELD, "n": 10, "k": 1, "ell": 2,
                    "log_blowup": 9, "log_final_poly_len": 0})
    * grinding_scale,
)

# --- provable Johnson (BGKTTZ 2024/1161 Thm 5.11 via cnifri Thm 1):
# fold term (m+1/2)^7 * |L0|^2 / (3 rho^{3/2} |F|), query (1-delta)^ell.
# The declared bound rounds the half-integer power 2^{(7n-3k)/2} UP to the
# next dyadic; soundness needs declared >= theorem, and the rounding is at
# most a factor sqrt(2) — both directions checked via squares (exact).
BIG_FIELD = 340282366762482138490186164457219031041
n, k, ell, m, delta = 10, 1, 2, 3, F(9, 10)
johnson_point = {
    "field_order": BIG_FIELD, "n": n, "k": k, "ell": ell,
    "log_blowup": n - k, "log_final_poly_len": 0,
    "m": m, "eta": F(1, 64), "delta": delta,
}
declared_fold = declared_round("zkc.rbr.fri.johnson", "fold", johnson_point)
theorem_fold_sq = (F((2 * m + 1) ** 7, 2**7)) ** 2 * F(2**67) / (3 * BIG_FIELD) ** 2
if not declared_fold**2 >= theorem_fold_sq:
    failures.append("johnson fold: the declared bound understates the theorem")
if not declared_fold**2 <= 2 * theorem_fold_sq:
    failures.append("johnson fold: the declared bound exceeds the dyadic rounding bound")
check(
    "johnson query term",
    (1 - delta) ** ell,
    declared_round("zkc.rbr.fri.johnson", "query", johnson_point),
)
if not declared_fold < (1 - delta) ** ell:
    failures.append("johnson composed: fold unexpectedly dominates")

# --- unique decoding (BCHKS 2025/2055 Cor 1.4): the exceptional-set bound is
# theta*n + 1 at block length n, valid for theta in [d/3, d/2 - 3/(d*n)] with
# distance d >= 3*sqrt(2/n). The fixture's theta = 63/128 at n = 10, k = 1,
# ell = 2; the rule prices the count at the initial block length 2^n (an upper
# bound for every fold round) and the queries at (1 - theta)^ell.
n, k, ell = 10, 1, 2
theta = F(63, 128)
udr_point = {"field_order": BIG_FIELD, "n": n, "k": k, "ell": ell,
             "log_blowup": n - k, "log_final_poly_len": 0, "theta": theta}
# the corollary's window at the LAST fold round (block 2^(n-k+1),
# distance 1 - 2^(k-1-n)) — the binding round as the domain shrinks:
d_last, n_last = 1 - F(1, 2 ** (n - k + 1)), 2 ** (n - k + 1)
if not (d_last / 3 <= theta <= d_last / 2 - F(3, 1) / (d_last * n_last)):
    failures.append("udr: the fixture theta is outside the corollary window")
if not d_last * d_last * n_last >= 18:
    failures.append("udr: the fixture domain is below the corollary floor")
# the exact radius (1-rho)/2 must sit OUTSIDE the window (the honesty boundary
# the invalid fixture pins): d/2 - theta_radius = 2^-(n+1) < 3/(d*n) for every
# d < 6 — i.e. always.
if F(1 - F(1, 2 ** (n - k)), 2) <= d_last / 2 - F(3, 1) / (d_last * n_last):
    failures.append("udr: the exact radius unexpectedly fits the window")
check(
    "udr fold term",
    (theta * 2**n + 1) / BIG_FIELD,
    declared_round("zkc.rbr.fri.udr", "fold", udr_point),
)
check(
    "udr query term",
    (1 - theta) ** ell,
    declared_round("zkc.rbr.fri.udr", "query", udr_point),
)

# --- field-size-linear Johnson (BCHKS 2025/2055 Thm 4.2 / Thm 1.5,
# substituted into the same RBR framework): the theorem's count is
#   (2*mh^5 + 3*mh*delta*rho_p)*n/(3*rho_p^{3/2}) + mh/sqrt(rho_p),
# mh = m + 1/2, at the paper's rho_p = rate - 1/n (= (2^k - 1)/2^n here). The
# rule spells it in dyadics of the rate rho = 2^-(n-k), rounding each
# half-integer exponent UP and carrying a 2^{3/2} (first term) or 2^{1/2}
# (second and third) margin that absorbs rho_p >= rho/2 (every k >= 1).
# Soundness needs declared >= theorem TERMWISE; the slack is bounded by 4 per
# term. sqrt comparisons are exact via squares.
n, k, ell, m, delta = 10, 1, 2, 3, F(9, 10)
mh = m + F(1, 2)
rho_p = F(2**k - 1, 2**n)
linear_point = {
    "field_order": BIG_FIELD, "n": n, "k": k, "ell": ell,
    "log_blowup": n - k, "log_final_poly_len": 0,
    "m": m, "eta": F(1, 64), "delta": delta,
}
declared_t1 = F(2, 3) * mh**5 * 2 ** ((5 * n - 3 * k + 3 + 1) // 2)  # ceil
declared_t2 = mh * delta * 2 ** ((3 * n - k + 1 + 1) // 2)
declared_t3 = mh * 2 ** ((n - k + 1 + 1) // 2)
thm_t1 = F(2, 3) * mh**5 * 2**n  # / rho_p^{3/2}
thm_t2 = mh * delta * 2**n       # / rho_p^{1/2}  (the rho_p cancels)
thm_t3 = mh                      # / rho_p^{1/2}
for name, declared_term, theorem_term, power in (
    ("t1", declared_t1, thm_t1, 3),
    ("t2", declared_t2, thm_t2, 1),
    ("t3", declared_t3, thm_t3, 1),
):
    if not declared_term**2 * rho_p**power >= theorem_term**2:
        failures.append(f"johnson-linear {name}: the declared term understates the theorem")
    if not declared_term**2 * rho_p**power <= 16 * theorem_term**2:
        failures.append(f"johnson-linear {name}: the declared term exceeds the slack cap")
# the multiplicity floor of Thm 1.5: m >= ceil(sqrt(rho_p)/(2*eta)) is implied
# by the decided 2*m*eta >= sqrt(rho) (squared, exact), at eta = 1/64:
eta = F(1, 64)
if not (2 * m * eta) ** 2 >= F(1, 2 ** (n - k)):
    failures.append("johnson-linear: the fixture m misses the multiplicity floor")
# the three terms as the signature composes them, at the fixture point where
# every exponent is an integer and the dyadic rounding is therefore exact:
check(
    "johnson-linear fold term",
    (declared_t1 + declared_t2 + declared_t3) / BIG_FIELD,
    declared_round("zkc.rbr.fri.johnson_linear", "fold", linear_point),
)
check(
    "johnson-linear query term",
    (1 - delta) ** ell,
    declared_round("zkc.rbr.fri.johnson_linear", "query", linear_point),
)
# an odd exponent point (n=11, k=1): the half-integer dyadic rounds UP — the
# declared bound never understates off the fixture grid either.
n2, k2 = 11, 1
rho2_p = F(2**k2 - 1, 2**n2)
r1 = F(2, 3) * mh**5 * 2 ** (-((5 * n2 - 3 * k2 + 3) // -2))
if not r1**2 * rho2_p**3 >= (F(2, 3) * mh**5 * 2**n2) ** 2:
    failures.append("johnson-linear odd exponent: the declared bound understates")

# --- the duplex-sponge FS chain (Chiesa-Orru eprint 2025/536 Thm 6.1 with
# Eq. 58): eps_fs(t) = eps_sr(t) + 25 t^2/|Sigma|^c + t * max_i eps_cdc_i
#   + sum_i eps_cdc_i,   eps_sr(t) = t * eps_rbr (CMS19/KPV19/COS20).
# Squeeze bias per mod_reduce challenge event: x uniform on [0, N),
# N = alphabet^symbols, target q: exactly r(q-r)/(Nq) with r = N mod q; a
# vector round of ell draws takes ell times that (TV subadditivity).
ALPHABET, CAPACITY = 256, 32
SIGMA_C = F(ALPHABET) ** CAPACITY


def squeeze_bias(q, symbols, count=1):
    N = ALPHABET**symbols
    r = N % q
    return count * F(r * (q - r), N * q)


def fs_coefficients(events):
    """The theorem's local duplex terms: (constant, t, t^2)."""
    biases = [squeeze_bias(*event) for event in events]
    return sum(biases), max(biases), F(25) / SIGMA_C


duplex_local = bound(
    RULES["zkc.fs.duplex"]["body"]["local_duplex_bound"],
    {
        "alphabet_order": ALPHABET,
        "capacity": CAPACITY,
        # the two codec-bias facts the path binding reads off the artifact
        "codec_bias_max": squeeze_bias(BIG_FIELD, 32),
        "codec_bias_sum": squeeze_bias(BIG_FIELD, 32) + squeeze_bias(1024, 32, 2),
    },
)
theorem_sum, theorem_max, theorem_quadratic = fs_coefficients(
    [(BIG_FIELD, 32), (1024, 32, 2)]
)
check("duplex constant term", theorem_sum, duplex_local.coefficient(0))
check("duplex t coefficient", theorem_max, duplex_local.coefficient(1))
check("duplex t^2 coefficient", theorem_quadratic, duplex_local.coefficient(2))

# the sumcheck squeeze is exact: 2^64 mod 2^61 = 0, so both codec terms vanish
# and the whole local bound is the quadratic sponge term alone.
sumcheck_local = bound(
    RULES["zkc.fs.duplex"]["body"]["local_duplex_bound"],
    {
        "alphabet_order": ALPHABET,
        "capacity": CAPACITY,
        "codec_bias_max": squeeze_bias(2**61, 8),
        "codec_bias_sum": squeeze_bias(2**61, 8) * 2,
    },
)
check("sumcheck duplex constant term", F(0), sumcheck_local.coefficient(0))
check("sumcheck duplex t coefficient", F(0), sumcheck_local.coefficient(1))
check("sumcheck duplex t^2 coefficient", theorem_quadratic,
      sumcheck_local.coefficient(2))

# every FRI rule must read its domain as a typed instance rather than infer it
for rule_id in (
    "zkc.rbr.fri.capacity",
    "zkc.rbr.fri.johnson",
    "zkc.rbr.fri.udr",
    "zkc.rbr.fri.johnson_linear",
    "zkc.rbr.fri.random_words",
    "zkc.rbr.fri.threshold_halving",
):
    if "fri_domain" not in declared_parameters(rule_id):
        failures.append(f"{rule_id}: no typed FRI-domain parameter")


# --- the corrected conjecture (Diamond-Gruen 2025/2010 §1.5): the query loss
# is (rho + eta)^ell with eta at or above (log2(e/rho) * rho) / log2 |F|; the
# fold term follows the conjectured accounting at list size one, n/|F|. The
# fixture prices eta_bar = 1/4096 at n = 10, k = 1: rho = 1/512, and the
# declared floor uses log2 e <= 1443/1000 and log2 |F| >= 127.
n, k, ell = 10, 1, 2
rho = F(1, 2 ** (n - k))
eta_bar = F(1, 4096)
floor = (F(1443, 1000) + (n - k)) * rho / 127
if not eta_bar >= floor:
    failures.append("random-words: the fixture eta_bar is below the correction floor")
rw_point = {"field_order": BIG_FIELD, "n": n, "k": k, "ell": ell,
            "log_blowup": n - k, "log_final_poly_len": 0, "eta_bar": eta_bar}
check(
    "random-words fold term",
    F(n, 1) / BIG_FIELD,
    declared_round("zkc.rbr.fri.random_words", "fold", rw_point),
)
check(
    "random-words query term",
    (rho + eta_bar) ** ell,
    declared_round("zkc.rbr.fri.random_words", "query", rw_point),
)

# --- threshold halving (2026/858): eps <= nR/|F| + (1 - delta/2)^q over
# delta in (1 - sqrt(rho), 1 - rho). Under this row family's rate convention
# nR = 2^k; the fixture prices delta = 63/64, strictly above the dyadic
# Johnson gate 1 - 2^-ceil((n-k)/2) = 31/32 and below 1 - rho = 511/512.
delta_th = F(63, 64)
if not (1 - F(1, 2 ** -(-(n - k) // 2)) < delta_th < 1 - rho):
    failures.append("threshold: the fixture delta is outside the cited window")
th_point = {"field_order": BIG_FIELD, "n": n, "k": k, "ell": ell,
            "log_blowup": n - k, "log_final_poly_len": 0, "delta": delta_th}
check(
    "threshold fold term",
    F(2**k, 1) / BIG_FIELD,
    declared_round("zkc.rbr.fri.threshold_halving", "fold", th_point),
)
check(
    "threshold query term",
    (1 - delta_th / 2) ** ell,
    declared_round("zkc.rbr.fri.threshold_halving", "query", th_point),
)

if failures:
    raise SystemExit("soundcalc mismatches:\n  " + "\n  ".join(failures))
print("soundcalc: every theorem-derived bound matches the declared bound")

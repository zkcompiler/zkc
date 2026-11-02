"""Exact textual replacement for bridge controls.

A control that mutates source, module or descriptor text must change exactly
the occurrence it names. Every textual mutation in the bridges uses
`replace_exactly_once`, which raises unless its pattern occurs exactly once and
its replacement differs, so a stale pattern can neither leave the text
unchanged nor change a second occurrence. A control that expects a refusal also
checks the diagnostic of its intended boundary: a mutation that fails earlier,
for example while the source is set up, is not a passing negative control.
"""


class ReplacementError(ValueError):
    """A replacement pattern does not occur exactly once, or does not change the text."""


def replace_exactly_once(text, old, new):
    """`text` with its single occurrence of `old` replaced by `new`."""
    if not isinstance(text, str) or not isinstance(old, str) or not isinstance(new, str) or not old:
        raise ReplacementError("a replacement needs text, a nonempty pattern and its replacement")
    if old == new:
        raise ReplacementError(f"the replacement of {old!r} does not change the text")
    count = text.count(old)
    if count != 1:
        raise ReplacementError(f"expected exactly one occurrence of {old!r}, found {count}")
    return text.replace(old, new)

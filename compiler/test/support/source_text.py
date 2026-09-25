"""Source text these tests share, and what they compare when position is not it.

The parser and the formatter both carry source positions through, and a test
that asks whether a record survived a round trip is asking about the record
rather than about the columns it came from. Two files wrote this stripper
identically.
"""

# What the compiler records about where a thing was written, which a test
# comparing meaning rather than layout has to set aside.
POSITIONS = ("span", "callSpan")


def unlocated(value):
    """The same record with every source position removed."""
    if isinstance(value, dict):
        return {
            key: unlocated(item)
            for key, item in value.items()
            if key not in POSITIONS
        }
    if isinstance(value, list):
        return [unlocated(item) for item in value]
    return value


# A helper whose name is exactly an operation's. Which category the frontend
# chooses is reported on two surfaces -- the elaboration report's `kind` and
# the encoded record's node tag -- and a test of either wants the same module,
# so it is written here rather than twice.
COLLISION = """module {
  fn "bool.and"<>(x: bool, y: bool) -> bool { return x; }
  fn Use<>(x: bool) -> bool { let y = bool::and(x, x); return y; }
}"""

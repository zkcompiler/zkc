"""Semantic and source-identity regressions from independent frontend reviews."""
import json
from commands import Commands
from source_text import COLLISION
from tools import records



commands = Commands(records())


def run(mode, text, refuses=None):
    """What the compiler printed, or what it said when it refused."""
    printed = commands.source(mode, text, refuses=refuses)
    return commands.last.stderr if refuses else printed


def common(text):
    return json.loads(run("protocol-source", text))


def report(text):
    return json.loads(run("protocol-inspect", text))


# A bound is an assumption, not a spelling for a sort. Their source identities
# differ even when the body is the same and both configurations are admissible.
weak = 'module { fn Id<F: domain Field>(x: F::Element) -> F::Element { return x; } }'
strong = weak.replace("domain Field", "Field")
assert report(weak)["snapshot"] != report(strong)["snapshot"]
weak_record = common(weak)
assert common(run("protocol-format", json.dumps(weak_record))) == weak_record

# Qualified primitives and exact helper names choose their categories before
# typechecking. A helper name matching an operation survives common printing.
# The elaboration report's view of the choice; frontend_pipeline.py checks the
# same choice as the encoded record's node tag, which is the other surface.
assert report(COLLISION)["elaborated_calls"][0]["kind"] == "operation"
helper = COLLISION.replace("bool::and(x, x)", '"bool.and"(x, x)')
assert report(helper)["elaborated_calls"][0]["kind"] == "algorithm"
helper_record = common(helper)
assert common(run("protocol-format", json.dumps(helper_record))) == helper_record
for name in ("let", "return", "yield", "attributes", "local"):
    quoted = helper.replace('"bool.and"', json.dumps(name))
    record = common(quoted)
    assert common(run("protocol-format", json.dumps(record))) == record

# Inference selects a deterministic member of the constraint-provided equality
# class. Swapping input order still changes the authored operation; it must not
# change the selected nominal argument. No artifact-equality claim is made.
equality = '''module {
  fn Add<F: Field, E: Field>(x: F::Element, y: E::Element) -> F::Element
    requires ("="(F, E)) { let z = field::add(x, y); return z; }
}'''
for text in (equality, equality.replace("add(x, y)", "add(y, x)")):
    assert report(text)["elaborated_calls"][0]["static_arguments"] == ["E"]
written = equality.replace("field::add(x, y)", "field::add::<F>(x, y)")
assert report(written)["elaborated_calls"][0]["static_arguments"] == ["F"]

# Malformed equality is rejected at its own declaration, before a later call
# could receive a misleading operand/type diagnostic.
malformed = '''module {
  fn Id<F: domain Field, G: domain Group>(x: F::Element) -> F::Element
  requires ("="(F, G)) { return x; }
}'''
error = run("protocol-source", malformed, "generic-equality-sort")
assert "-:3:13:" in error, error
run("protocol-source", malformed.replace('"="(F, G)', '"="(F)'), "generic-predicate-arity")
run("protocol-source", malformed.replace('"="(F, G)', 'Field(G)'), "generic-predicate-sort")

# Generic records may name parameters/projections, not closed catalog identities.
run("protocol-source", '''module {
  fn Bad<F: Field>(x: koala-bear::Element) -> koala-bear::Element { return x; }
}''', "source-generic-term")
run("protocol-source", weak.replace("{ return x; }", "requires (Field(koala-bear)) { return x; }"),
    "source-generic-term")
wrong_sort = '''module {
  fn Id<F: domain Field>(x: F::Element) -> F::Element { return x; }
  fn Use<G: ScalarAction>(x: G::Scalar::Element) -> G::Scalar::Element {
    let y = Id::<G>(x); return y;
  }
}'''
run("protocol-source", wrong_sort, "source-static-sort")

# Concrete associated projections are resolved at the configuration boundary,
# including the emitted record, rather than only in a private inferred signature.
config = weak[:-1] + ' configure Closed = Id(F = "bls12-381.g1"::Scalar); }'
assert common(config) == common(config.replace('"bls12-381.g1"::Scalar', '"bls12-381.fr"'))

# Empty generic signatures still require explicit protocol-local configuration.
local = '''module {
  fn Id<>(x: bool) -> bool { return x; }
  configure Closed = Id();
  protocol Demo { roles (P); inputs (P x: bool); outputs (P bool);
    local P: let y = Closed(x); return y; }
}'''
common(local)
run("protocol-source", local.replace("Closed(x)", "Id(x)"), "source-local-configuration")

# Convenience profiles are a supported closed-module shorthand. They neither
# introduce generic scope nor provide arbitrary omitted type parameters.
profile = '''module "arkworks.bls12-381/1" {
  fn Identity(x: field) -> field origin Chosen() { return x; }
}'''
assert common(profile)[2][0][-1] == ["Chosen", []]
run("protocol-source", profile.replace("Identity(x", "Identity<>(x"), "source-profile-generic")
run("protocol-source", profile.replace("field", "vector"), "source-type")

print(f"frontend elaboration: {commands.save()} review regression checks passed")

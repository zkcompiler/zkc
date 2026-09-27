"""Installed declarations use source resolution without global primitive names."""

import json

from cases import case
from commands import Commands
from tools import records


commands = Commands(records())


def common(text):
    return json.loads(commands.source("protocol-source", text))


POLYNOMIAL = """
  use zkc::algebra;
  use zkc::poly::{Polynomial, evaluate};
  fn Evaluate<F: algebra::CommRing>(p: Polynomial<F>, x: F::Element)
      -> F::Element { return evaluate::<F>(p, x); }
"""

with case("installed type and operation aliases preserve logical identity"):
    expected = common(POLYNOMIAL)
    renamed = POLYNOMIAL.replace("Polynomial, evaluate", "Polynomial as Poly, evaluate as at")
    renamed = renamed.replace("p: Polynomial<F>", "p: Poly<F>").replace("return evaluate", "return at")
    assert common(renamed) == expected
    assert common(POLYNOMIAL.replace("return evaluate", "return zkc::poly::evaluate")) == expected
    assert common(commands.source("protocol-format", json.dumps(expected))) == expected

with case("no implicit source primitive namespace"):
    commands.source("protocol-source", POLYNOMIAL.replace("return evaluate", "return poly::univariate_evaluate"),
                    refuses="source-name-unresolved")

with case("no implicit domain type constructor"):
    commands.source("protocol-source", POLYNOMIAL.replace("{Polynomial, evaluate}", "evaluate"),
                    refuses="source-name-unresolved")

with case("installed primitive is not a type"):
    commands.source("protocol-source", POLYNOMIAL.replace("p: Polynomial<F>", "p: evaluate<F>"),
                    refuses="source-name-kind")

with case("ordinary helpers keep identity beside installed primitive names"):
    text = """
      use zkc::algebra;
      fn Add<F: algebra::Field>(x: F::Element, y: F::Element) -> F::Element { return x; }
      fn Caller<F: algebra::Field>(x: F::Element, y: F::Element) -> F::Element {
        let a = Add::<F>(x, y);
        return algebra::add::<F>(a, y);
      }
    """
    encoded = json.dumps(common(text))
    assert '"apply"' in encoded and '"field.add"' in encoded

with case("element families reduce to existing logical types"):
    text = """
      use zkc::algebra::Vector;
      use zkc::algebra::Matrix;
      fn Fields<F: domain Field>(x: Vector<F::Element>) -> Vector<F::Element> { return x; }
      fn Groups<G: domain Group>(x: Vector<G::Element>) -> Vector<G::Element> { return x; }
      fn Matrices<F: domain Field>(x: Matrix<F::Element>) -> Matrix<F::Element> { return x; }
    """
    encoded = json.dumps(common(text))
    assert '"vector:F"' in encoded and '"groups:G"' in encoded and '"matrix:F"' in encoded
    commands.source("protocol-source", text.replace("Matrix<F::Element>", "Matrix<bool>"),
                    refuses="source-type")

with case("construction-only operations cannot be directly bound in source"):
    commands.source("protocol-source", '''
      bind Draw = "transcript.challenge"("merlin.bls12-381.fr/1");
    ''', refuses="source-operation-stage")

with case("construction-only operations cannot be imported"):
    commands.source("protocol-source", " use zkc::transcript::challenge; ",
                    refuses="source-name-unresolved")

with case("generated symbols cannot impersonate installed declarations"):
    commands.source("protocol-source", " fn __installed_operation_field_add(x: bool) -> bool { return x; } ",
                    refuses="source-name-reserved")

with case("reserved root declarations retain diagnostic bookkeeping"):
    for declaration in (
        "bind zkc = \"bool.and\"();",
        "fn zkc(x: bool) -> bool { return x; }",
        "struct zkc { x: bool }",
    ):
        commands.source("protocol-source", declaration,
                        refuses="source-name-reserved")

with case("profile module headings are retired"):
    commands.source("protocol-source", "module bls12-381 { fn Identity(x: bool) -> bool { return x; } }",
                    refuses="source-module-wrapper")

with case("qualified capability requirements use the ordinary name resolver"):
    base = """
      use zkc::algebra;
      fn Add<F: domain Field>(x: F::Element, y: F::Element) -> F::Element
          requires (algebra::Field(F)) { algebra::add(x, y) }
    """
    expected = common(base)
    assert common(base.replace("requires (algebra::Field(F))", "where F: algebra::Field")) == expected
    assert common(base.replace("requires (algebra::Field(F))", "where algebra::Field(F)")) == expected

with case("carriers do not share installed source symbol names"):
    for symbol in ("__installed_operation_field.add", "__installed_type_field",
                   "__installed_capability_Field"):
        # Exact carrier names that are not identifiers are quoted.
        name = symbol if symbol.isidentifier() else json.dumps(symbol)
        text = f"""carrier module {{
          fn {name}(x: Polynomial<"bn254.fr">) -> Polynomial<"bn254.fr"> {{ return x; }}
        }}"""
        expected = common(text)
        assert common(commands.source("protocol-format", json.dumps(expected))) == expected

with case("carrier type paths distinguish exports with the same member name"):
    text = """carrier module {
      fn Scalar(x: zkc::algebra::Element<"bn254.fr">) -> zkc::algebra::Element<"bn254.fr"> { return x; }
      fn Point(x: zkc::curve::Element<"bn254.g1">) -> zkc::curve::Element<"bn254.g1"> { return x; }
    }"""
    value = common(text)
    assert '"field:bn254.fr"' in json.dumps(value)
    assert '"group:bn254.g1"' in json.dumps(value)
    assert common(commands.source("protocol-format", json.dumps(value))) == value
    # The carrier reader has no authored name resolution: an export that is
    # ambiguous without its module path is not a carrier type.
    commands.source("protocol-source", text.replace("zkc::curve::Element", "Element"),
                    refuses="source-syntax")

with case("installed root cannot be a dependency alias"):
    commands.source("protocol-source", '''
      dependency zkc = library(namespace="test", name="missing", version="1", resolution="one");
    ''', refuses="source-name-reserved")

with case("natural attribute slots follow their declared contract"):
    text = """
      use zkc::algebra;
      const Size: index = 2;
      fn Select<F: algebra::Field>(m: algebra::Vector<F::Element>) -> algebra::Vector<F::Element> {
        algebra::vector_gather(m) attributes(Size)
      }
    """
    expected = common(text)
    assert common(text.replace("attributes(Size)", "attributes(2)")) == expected

with case("matrix identity attributes remain opaque digests"):
    digest = 'a' * 64
    text = f'''
      use zkc::algebra;
      fn Check<F: algebra::Field>(m: algebra::Matrix<F::Element>) -> bool {{
        algebra::matrix_identity_check(m) attributes("{digest}")
      }}
    '''
    assert common(text.replace(f'"{digest}"', digest)) == common(text)

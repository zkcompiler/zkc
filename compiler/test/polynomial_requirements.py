"""Unambiguous independent polynomial requirements and preparation boundaries."""

import copy
import hashlib
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
fixtures = Path(__file__).parent / "fixtures/mathematical"
source = (fixtures / "sumcheck.mlir").read_text()
requirements = json.loads((fixtures / "sumcheck.requirements.json").read_text())
canonical = json.dumps(requirements, separators=(",", ":"))
source_path = OUT / "source.mlir"
source_path.write_text(source)
requirement_path = OUT / "requirements.json"
candidate_path = OUT / "candidate.mlir"
candidate_path.write_text(
    commands.verified(source, None, "--zkc-project-protocol=simplify=false")
)


def check(text, refuses=None):
    requirement_path.write_text(text)
    result = commands.run(
        [
            compiler,
            "protocol-check-reductions",
            source_path,
            requirement_path,
            candidate_path,
        ],
        refuses=refuses,
    )
    return json.loads(result) if refuses is None else None


def checked(text, program=source, refuses=None):
    requirement_path.write_text(text)
    result = commands.source(
        "protocol-checked-bundle",
        program,
        "--entry=reduction",
        f"--requirements={requirement_path}",
        refuses=refuses,
    )
    return json.loads(result) if refuses is None else None


with case("ordinary requirements establish the original sumcheck boundary"):
    report = check(canonical)
    assert [r["arity"] for r in report["requirements"]] == [2]

# Cover every index position, so a stricter scalar reader cannot leave index
# arrays or a less common residual/terminal port using LLVM's float coercion.
record = requirements["requirements"][0]
for key in (
    "claim",
    "service",
    "residual_scalar",
    "terminal_scalar",
    "decision",
    "subjects",
    "residual_subjects",
    "residual_point",
    "terminal_subjects",
    "terminal_point",
):
    value = record[key]
    prefix = f'"{key}":' + ("[" if isinstance(value, list) else "")
    number = str(value[0] if isinstance(value, list) else value)
    for token in (
        number + ".0",
        number + "e0",
        number + "E+0",
        "-0",
        "+" + number,
        "0" + number,
    ):
        with case(f"{key} rejects numeric spelling {token}"):
            check(
                canonical.replace(prefix + number, prefix + token, 1),
                "polynomial-requirement-format",
            )

for label, malformed in (
    ("top-level", '{"format":"other",' + canonical[1:]),
    ("escaped top-level", '{"\\u0066ormat":"other",' + canonical[1:]),
    ("nested scalar", canonical.replace('"claim":2', '"claim":99,"claim":2')),
    ("escaped scalar", canonical.replace('"claim":2', '"\\u0063laim":99,"claim":2')),
    (
        "replaced object with additional keys",
        '{"requirements":{"discarded":{"field":1}},' + canonical[1:],
    ),
):
    with case(f"duplicate {label} keys are not last-wins premises"):
        check(malformed, "polynomial-requirement-format")
        checked(malformed, refuses="polynomial-requirement-format")

with case("nested optional composition keys obey the same policy"):
    composed = copy.deepcopy(requirements)
    composed["requirements"][0]["composition"] = {
        "entry": "main",
        "reduction_site": "reduce",
        "terminal_site": "decide",
    }
    text = json.dumps(composed).replace(
        '"entry": "main"', '"entry":"other","\\u0065ntry":"main"'
    )
    # Lexical refusal precedes the nonexistent composition entry.
    check(text, "polynomial-requirement-format")

for label, malformed in (
    ("surrogate escape", canonical.replace("public-sumcheck", r"\ud800")),
    ("bad escape", canonical.replace("public-sumcheck", r"\q")),
    ("trailing value", canonical + "{}"),
):
    with case(f"malformed JSON {label} is refused"):
        check(malformed, "polynomial-requirement-format")

with case("whitespace key order and escaped unique keys preserve meaning"):
    alternate = json.dumps(requirements, indent=2, sort_keys=True).replace(
        '"claim"', '"\\u0063laim"'
    )
    assert check(alternate) == check(canonical)
    first, second = checked(canonical), checked(alternate)
    assert first["bundle"] == second["bundle"]
    assert (
        first["correspondence"]["requirements_sha256"]
        == second["correspondence"]["requirements_sha256"]
    )
    assert (
        second["correspondence"]["requirements_input_sha256"]
        == hashlib.sha256(alternate.encode()).hexdigest()
    )
    assert (
        first["correspondence"]["requirements_input_sha256"]
        != second["correspondence"]["requirements_input_sha256"]
    )

with case("numeric-looking strings and valid surrogate pairs stay strings"):
    named = copy.deepcopy(requirements)
    named["requirements"][0]["id"] = '1.0e-2+00\\"\U0001f642'
    result = check(json.dumps(named))
    assert result["requirements"][0]["id"] == named["requirements"][0]["id"]

for label, text, code in (
    (
        "64 levels reach grammar admission",
        "[" * 64 + "]" * 64,
        "polynomial-requirement-format",
    ),
    ("65 levels exceed the nesting bound", "[" * 65, "polynomial-requirement-limit"),
    (
        "one MiB reaches grammar admission",
        " " * (1024 * 1024),
        "polynomial-requirement-format",
    ),
    (
        "over one MiB exceeds the byte bound",
        " " * (1024 * 1024 + 1),
        "byte-limit",
    ),
):
    with case(label):
        check(text, code)

with case("record identity duplicates keep their semantic diagnostic"):
    duplicate = copy.deepcopy(requirements)
    duplicate["requirements"] *= 2
    check(json.dumps(duplicate), "polynomial-requirement-duplicate")

for helper in (
    "func.func private @unused(%x: i32) -> i32 { return %x : i32 }",
    "func.func private @unused() { func.call @unused() : () -> () return }",
):
    with case(f"invalid unused helper is admitted before erasure: {helper}"):
        invalid = source.replace("}) {profile=", helper + "\n}) {profile=")
        for option in (
            "--zkc-project-protocol",
            "--zkc-project-protocol=simplify=false",
        ):
            commands.verified(invalid, "mathematical-formation", option)
        commands.source(
            "protocol-bundle",
            invalid,
            "--entry=reduction",
            refuses="mathematical-formation",
        )
        # Source admission precedes requirement parsing in checked compilation.
        checked("{", program=invalid, refuses="mathematical-formation")

with case("unused invalid polynomial observation precedes folding and requirements"):
    marker = ' %coefficients0 = "poly.coefficients"'
    extra = ' %unused = "poly.coefficients"(%round0) : (!poly.polynomial<"bls12-381.fr", 1>) -> tensor<2x!algebra.field<"bls12-381.fr">>\n'
    invalid = source.replace(marker, extra + marker)
    checked("{", program=invalid, refuses="polynomial-formation")



with case("fusion preparation choice is explicit in independent and compiled reports"):
    requirement_path.write_text(canonical)
    fused = commands.verified(source, None,
                              "--zkc-project-protocol=simplify=false fuse-vector-reductions=true")
    candidate_path.write_text(fused)
    checked_report = json.loads(commands.run([
        compiler, "protocol-check-reductions", source_path, requirement_path,
        candidate_path, "--fuse-vector-reductions",
    ]))
    assert checked_report["fuse_vector_reductions"] is True
    compiled = json.loads(commands.source(
        "protocol-checked-bundle", source, "--entry=reduction",
        f"--requirements={requirement_path}", "--fuse-vector-reductions",
    ))
    assert compiled["correspondence"]["fuse_vector_reductions"] is True


field = '!algebra.field<"bls12-381.fr">'
vector = f'tensor<?x{field}>'
fusable = f'''
 "local.binding"() {{sym_name="vf_sum",contract="vector.sum",arguments=["bls12-381.fr"],implementation=""}} : ()->()
 func.func private @vf_mul(%x:{field},%y:{field})->{field} {{
   %r = "algebra.field_multiply"(%x,%y) : ({field},{field})->{field}
   func.return %r : {field}
 }}
 algebra.map_realize @vf_map = @vf_mul [true,true] : ({vector},{vector})->{vector}
 local.func @vf_work(%a:{vector},%b:{vector})->{field} attributes {{logical_origin=["vf_work",[]]}} {{
   %v = local.apply @vf_map(%a,%b) {{site="map"}} : ({vector},{vector})->{vector}
   %r = "algebra.exec.vector_sum"(%v) {{binding=@vf_sum,parameters=[],site="sum"}} : ({vector})->{field}
   local.return %r : {field}
 }}
'''
with case("independent reduction checker rejects mismatched preparation choices"):
    # Even an unused executable local is frozen by the structural checker.
    mixed = source.replace('module { "protocol.module"() ({',
                           'module { "protocol.module"() ({' + fusable, 1)
    source_path.write_text(mixed)
    requirement_path.write_text(canonical)
    for fuse in (False, True):
        choice = 'true' if fuse else 'false'
        candidate = commands.verified(
            mixed, None, f'--zkc-project-protocol=simplify=false fuse-vector-reductions={choice}')
        assert ('algebra.exec.vector_dot' in candidate) == fuse
        candidate_path.write_text(candidate)
        flags = ['--fuse-vector-reductions'] if fuse else []
        commands.run([compiler, 'protocol-check-reductions', source_path,
                      requirement_path, candidate_path, *flags])
        opposite = [] if fuse else ['--fuse-vector-reductions']
        commands.run([compiler, 'protocol-check-reductions', source_path,
                      requirement_path, candidate_path, *opposite],
                     refuses='polynomial-correspondence-declaration')

print(f"polynomial requirements: {counted()} cases")

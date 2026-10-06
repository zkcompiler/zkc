"""A public-table Sumcheck with actual reduction-to-terminal composition."""

from pathlib import Path


def composed_sumcheck():
    fixtures = Path(__file__).resolve().parents[1] / "fixtures/mathematical"
    source = (fixtures / "sumcheck.mlir").read_text()
    field = '!algebra.field<"bls12-381.fr">'
    array = f"tensor<4x{field}>"
    service = '!protocol.service_ref<"random.bls12-381.fr/1">'
    inputs = f"{array}, {array}, {field}, {service}"
    residual = ", ".join([array, array, field, field, field, field, field])
    terminal = ", ".join([array, array, field, field, field])
    wrapper = f""""protocol.func"() ({{^bb0(%t:{array},%u:{array},%c:{field},%s:{service}):
 %r:7 = protocol.apply @reduction(%t,%u,%c,%s) {{roles=["Prover","Checker"],site="reduce"}} : ({inputs}) -> ({residual})
 %d = protocol.apply @terminal(%r#0,%r#1,%r#2,%r#3,%r#4) {{roles=["Checker"],site="decide"}} : ({terminal}) -> i1
 "protocol.return"(%d) : (i1)->()}}) {{sym_name="main",function_type=({inputs})->i1,
 roles=["Prover","Checker"],input_roles=[["Prover","Checker"],["Prover","Checker"],["Prover","Checker"],["Checker"]],output_roles=[["Checker"]]}} : () -> ()
"""
    return source.replace(
        "}) {profile=#protocol.profile<protocol>}",
        wrapper + "}) {profile=#protocol.profile<protocol>}",
    )

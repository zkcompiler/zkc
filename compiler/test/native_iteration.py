"""Compact structured iteration, count agreement and exact common formation."""
import json
from pathlib import Path
from cases import case, counted
from commands import Commands
from tools import records
from variant_codec import descriptor
OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures/mathematical'
for name, fixture in [('evaluate', 'recipe-evaluate'), ('constant', 'constant-sumcheck'), ('demand', 'iteration-demand'), ('repeat', 'iteration'), ('nested', 'nested-iteration'), ('data', 'structured-data'), ('sumcheck', 'iterated-sumcheck'), ('traces', 'optional-traces'), ('cubic', 'cubic-sumcheck'), ('layers', 'layered-sumcheck'), ('weighted', 'weighted-fold')]:
    source = (FIXTURES / (fixture + '.mlir')).read_text()
    with case(name + ' compact compiler bundle'):
        for suffix, options in [('', ()), ('_plain', ('--no-simplify',)), ('_release', ('--release-storage',))]:
            result = commands.source('protocol-bundle', source, *options)
            bundle = json.loads(result)
            assert bundle['format'] == 'zkc.run'
            assert json.loads(bundle['candidate'])[0] == 'zkc.program'
            (OUT / (name + suffix + '.bundle')).write_text(result)
        if 'maximum=8:i64' not in source:
            assert name in ('evaluate', 'data', 'traces')
            continue
        # A larger maximum changes only the bound, never copies body actions.
        large = json.loads(commands.source('protocol-bundle', source.replace('maximum=8:i64','maximum=100000:i64')))
        small = json.loads(commands.source('protocol-bundle', source))
        assert len(large['steps']) == len(small['steps'])
        assert len(large['candidate']) < len(small['candidate']) + 100
with case('reject unavailable count and forged carried availability'):
    source = (FIXTURES / 'iteration.mlir').read_text()
    commands.source('protocol-bundle', source.replace('input_roles=[["P", "V"],','input_roles=[["P"],'), refuses='mathematical-formation')
    commands.source('protocol-bundle', source.replace('carried_roles=[["P"]]', 'carried_roles=[["P", "V"]]'), refuses='mathematical-formation')
with case('reject malformed bound and duplicate nested sites'):
    commands.source('protocol-bundle', source.replace('maximum=8:i64','maximum=-1:i64'), refuses='mathematical-formation')
    nested = (FIXTURES / 'nested-iteration.mlir').read_text()
    commands.source('protocol-bundle', nested.replace('site="inner"','site="outer"'), refuses='mathematical-formation')
with case('stable recipe ABI and malformed declarations'):
    recipe = (FIXTURES / 'iterated-sumcheck.mlir').read_text()
    # A simplifier may lower the expression degree without changing the declared
    # message bound or the exact realization signature.
    commands.source('protocol-bundle', recipe.replace('"poly.recipe_yield"(%p)', '"poly.recipe_yield"(%a)'))
    for old, new in [
        ('degree=2:i64', 'degree=1:i64'),
        ('degree=2:i64', 'degree=17:i64'),
        ('recipe=@product', 'recipe=@missing'),
        ('algebra.field_multiply %a, %b', 'algebra.field_equal %a, %b'),
    ]:
        commands.source('protocol-bundle', recipe.replace(old, new), refuses='polynomial-formation' if 'field_equal' not in new else 'result')
    # Generic malformed siblings must refuse, not crash before symbol checking.
    commands.source('protocol-bundle', recipe.replace('"poly.recipe_yield"(%p) : (!f)->()', '"poly.recipe_yield"() : ()->()'), refuses='operand')
    commands.source('protocol-bundle', recipe.replace('%p = algebra.field_multiply %a, %b : (!f,!f)->!f', '%p = "algebra.constant"() {wrong="0"} : ()->!f'), refuses='value')
with case('exact affine roots through zero or many iterations'):
    affine = '''!r = !local.capability<"rng:bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%n:ui64,%a:!r,%b:!r):
   %out:2 = "protocol.repeat"(%n,%a,%b) ({ ^body(%i:ui64,%left:!r,%right:!r):
     "protocol.yield"(%left,%right) : (!r,!r)->()
   }) {site="roots",carried=2:i64,maximum=8:i64,roles=["P"],carried_roles=[["P"],["P"]]} : (ui64,!r,!r)->(!r,!r)
   "protocol.return"(%out#0,%out#1) : (!r,!r)->()
 }) {sym_name="main",function_type=(ui64,!r,!r)->(!r,!r),roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"],["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
'''
    commands.source('protocol-bundle', affine)
    commands.source('protocol-bundle', affine.replace('"protocol.yield"(%left,%right)', '"protocol.yield"(%right,%left)'), refuses='mathematical-formation')
with case('nested unused polynomial observation is checked before DCE'):
    source = (FIXTURES / 'iterated-sumcheck.mlir').read_text()
    extra = '''     %too_small = "poly.coefficients"(%q) : (!q)->tensor<1x!f>
'''
    commands.source('protocol-bundle', source.replace('     %zero =', extra + '     %zero ='), refuses='polynomial-formation')
with case('statement bindings stay at entry'):
    source = (FIXTURES / 'iterated-sumcheck.mlir').read_text()
    declaration = ''' "relation.declare"() {sym_name="claim_relation",kind="external",key="example/claim",revision="1",signature=(!f)->i1,purposes=["statement"]} : ()->()
'''
    statement = '''     "protocol.statement"(%current) {relation=@claim_relation,selectors=["V"],acceptance=0:i64} : (!f)->()
'''
    source = source.replace(' "poly.recipe"', declaration + ' "poly.recipe"').replace('     %coeffs =', statement + '     %coeffs =')
    commands.source('protocol-bundle', source, refuses="expects parent op 'protocol.func'")
with case('application role roster cannot escape enclosing repeat'):
    source = (FIXTURES / 'layered-sumcheck.mlir').read_text()
    # W is a legal outer role but not a participant of the inner round segment.
    source = source.replace('sym_name="main",function_type=(ui64,!rng)->i1,roles=["P","V"]', 'sym_name="main",function_type=(ui64,!rng)->i1,roles=["P","V","W"]')
    source = source.replace('roles=["P","V"],site="reduce"', 'roles=["P","W"],site="reduce"')
    commands.source('protocol-bundle', source, refuses='mathematical-formation')
with case('typed Groth16 proof product retains nominal group fields'):
    proof = descriptor('Groth16Proof', [('proof', ['group:bn254.g1', 'group:bn254.g2', 'group:bn254.g1'])])
    source = f'''!g1 = !algebra.group<"bn254.g1">
!g2 = !algebra.group<"bn254.g2">
!proof = !local.variant<"{proof}">
module {{ "protocol.module"() ({{
 "protocol.func"() ({{ ^entry(%a:!g1,%b:!g2,%c:!g1):
   %p = "data.make"(%a,%b,%c) {{alternative="proof"}} : (!g1,!g2,!g1)->!proof
   %middle = "data.get"(%p) {{index=1:i64}} : (!proof)->!g2
   "protocol.return"(%p,%middle) : (!proof,!g2)->()
 }}) {{sym_name="main",function_type=(!g1,!g2,!g1)->(!proof,!g2),roles=["V"],input_roles=[["V"],["V"],["V"]],output_roles=[["V"],["V"]]}} : ()->()
}}) {{profile=#protocol.profile<protocol>}} : ()->() }}
'''
    bundle = json.loads(commands.source('protocol-bundle', source))
    assert bundle['format'] == 'zkc.run'
    commands.source('protocol-bundle', source.replace('index=1:i64', 'index=2:i64'), refuses='mathematical-formation')
with case('preparation retains tensor construction from scalar constants'):
    source = '''!f = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
 "protocol.func"() ({
   %a = "algebra.constant"() {value="1"} : ()->!f
   %b = "algebra.constant"() {value="2"} : ()->!f
   %xs = tensor.from_elements %a, %b : tensor<2x!f>
   "protocol.return"(%xs) : (tensor<2x!f>)->()
 }) {sym_name="main",function_type=()->tensor<2x!f>,roles=["P"],input_roles=[],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
'''
    prepared = commands.verified(source, None, '--zkc-prepare-protocol')
    assert 'tensor.from_elements' in prepared
    assert 'arith.constant dense' not in prepared
    commands.source('protocol-bundle', prepared)
counted()

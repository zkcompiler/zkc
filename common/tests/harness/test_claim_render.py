"""Wire rendering preserves request data; it never interprets registry meanings."""

from copy import deepcopy
import pytest
from harness import load


def renderer():
    return load('claim_render', 'lean/bridges/pipeline/claim_render.py')


def application(name, arguments=None):
    return {'kind':'application', 'name':name, 'version':0,
            'arguments':[] if arguments is None else arguments}


def request():
    return {'subject':{'unit':'sha256:unit', 'entry':'example::Proof',
                       'stage':'compiled-ideal','artifacts':[]},
            'property':{'name':'soundness','version':0},
            'model':application('models.fiat_shamir'),
            'target':{'protocol':'actual-protocol','language':application('languages.guess')},
            'accept':{'output':True,'port':0,'role':1,'path':[]},
            'quantity':{'kind':'scalar','expression':{'kind':'natural','value':'0'}},
            'capabilities':[]}


def test_imported_protocol_is_part_of_typed_wire_data():
    first=request()
    second=deepcopy(first)
    second['target']['protocol']='another-protocol'
    assert renderer().request(first)!=renderer().request(second)
    assert '.importedLanguage "actual-protocol"' in renderer().request(first)


def test_imported_arguments_remain_data_for_lean_to_accept_or_refuse():
    value=request()
    value['target']['language']['arguments']=[{'label':'offset','value':{'kind':'natural','value':'7'}}]
    result=renderer().request(value)
    assert '(some "offset", (.natural 7))' in result
    assert 'languages.guess' in result


@pytest.mark.parametrize('bad',[True,-1,1.5,'2'])
def test_versions_and_indices_are_actual_naturals(bad):
    value=request()
    value['property']['version']=bad
    with pytest.raises(ValueError):
        renderer().request(value)


@pytest.mark.parametrize('bad',['00','+1','-1','1.0','1e2','1_000'])
def test_noncanonical_expression_naturals_are_refused(bad):
    with pytest.raises(ValueError):
        renderer().expression({'kind':'natural','value':bad})


def test_registry_names_are_quoted_data_not_lean_declarations():
    value=request()
    value['property']['name']='x"\naxiom forged : False --'
    result=renderer().request(value)
    assert 'axiom forged' in result
    assert '\naxiom forged' not in result
    assert 'x\\"\\naxiom forged' in result


def test_unknown_fields_are_not_silently_dropped():
    value=request()
    value['target']['invented']=True
    with pytest.raises(ValueError):
        renderer().request(value)

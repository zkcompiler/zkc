"""Admitted-source domain facts: exact expressions, hostile reception, coverage.

What the independent Lean consumer makes of the same source is a separate test,
tests/protocol/test_polynomial_domains_reference.py, because it needs a second build.
"""
import json
from commands import Commands
from tools import corpus, records



commands = Commands(records())


def run(command, text, *args, refuses=None):
    """What the compiler answered, read as JSON, or the refusal itself."""
    printed = commands.source(command, text, *args, refuses=refuses)
    return commands.last if refuses else json.loads(printed)


def inspect(text, pair=None):
    args = ['main'] + ([f'--compare={pair[0]},{pair[1]}'] if pair else [])
    return run('domain-inspect', text, *args)


def relation(source, left, right, expected, reason=None):
    c = inspect(source, (left, right))['comparison']
    assert c['relation'] == expected, c
    assert c['reasons'], c
    if reason:
        assert reason in c['reasons'], c


source = corpus.joinpath('polynomial-domains.pir').read_text().rstrip('\n')
report = inspect(source)
assert inspect(json.dumps(run('protocol-source', source))) == report
assert report['format'] == 'zkc.polynomial-domains/1'
domains = report['domains']
assert len(domains) == 10, domains
assert [d['association'] for d in domains].count('fold-result') == 1
assert all(d['field'] == 'koala-bear' for d in domains)
convention = domains[0]['convention']
assert convention['max_log_size'] == 24
assert convention['maximal_root'] == '1791270792'
assert convention['root_field'] == 'koala-bear'
assert all(d['convention'] == convention for d in domains)
for i in range(1, 6):
    relation(source, 0, i, 'same')
    assert domains[0]['congruence_class'] == domains[i]['congruence_class']
relation(source, 0, 6, 'different', 'size-positive-domain-versus-half')
relation(source, 6, 7, 'same')
relation(source, 6, 8, 'same')
relation(source, 0, 9, 'unknown', 'shift-equality-unproved')
assert [u['compatibility']['relation'] for u in report['uses']] == [
    'same', 'same', 'same', 'unknown']
terms = report['terms']
assert terms[domains[6]['size']]['kind'] == 'half'
assert terms[domains[6]['shift']]['kind'] == 'square'
for name in ('back', 'coefficients', 'scalar'):
    value = next(v for v in report['values'] if v['name'] == name)
    assert value['domain'] is None
    assert value['unknown_reason'] == 'no-installed-domain-transfer'
    assert value['may_depend_on']  # a dependency is not a coset identity

# Exact numeric constants from distinct operations; different shifts mean
# different ORDERED domains, without claiming the underlying sets are disjoint.
constants = '''module {
  fn Points<F: domain Field>()->() requires(TwoAdicField(F)) {
    let four = index::constant() attributes ("4"); let eight = index::constant() attributes ("8");
    let two = field::constant::<F>() attributes ("2"); let three = field::constant::<F>() attributes ("3");
    let again = field::constant::<F>() attributes ("2");
    let a = poly::domain_points::<F>(two,four);
    let b = poly::domain_points::<F>(three,four);
    let c = poly::domain_points::<F>(two,eight);
    let d = poly::domain_points::<F>(again,four);
    return ();
  }
  configure Base=Points(F=koala-bear);
  configure Extension=Points(F=koala-bear.ext8-binomial3);
  protocol Main { roles(P); local P:Base(); local P:Extension(); return(); }
  instance main_instance:Main {roles(P=P);} entry main=main_instance;
}'''
relation(constants, 0, 1, 'different', 'shift-distinct-canonical-constants')
relation(constants, 0, 2, 'different', 'size-distinct-canonical-constants')
relation(constants, 0, 3, 'same')
relation(constants, 0, 4, 'different', 'distinct-nominal-fields')
extended = inspect(constants)['domains'][4]
assert extended['field'] == 'koala-bear.ext8-binomial3'
assert extended['convention'] == convention

receptions = '''module {
  bind points=poly::domain_points(koala-bear);
  bind interpolate=poly::coset_interpolate(koala-bear);
  fn Points(s:koala-bear::Element,n:index)->(Vector<koala-bear::Element>) {
    let v = points(s,n); return(v);
  }
  fn Alias(s:koala-bear::Element)->(koala-bear::Element) {return(s);}
  fn Back(v:Vector<koala-bear::Element>,s:koala-bear::Element)->() {
    let p = interpolate(v,s); return();
  }
  protocol Main {
    roles(P,V); inputs(P s:koala-bear::Element,P n:index);
    local P:let sent = Points(s,n);
    message size:P(n)->V(n1);
    message first:P(s)->V(s1);
    message second:P(s)->V(s2);
    message word:P(sent)->V(received);
    local V:let a = Points(s1,n1);
    local V:let alias = Alias(s1);
    local V:let b = Points(alias,n1);
    local V:let c = Points(s2,n1);
    local V:Back(received,s1);
    return();
  }
  instance main_instance:Main {roles(P=P,V=V);} entry main=main_instance;
}'''
relation(receptions, 0, 1, 'unknown', 'size-equality-unproved')
relation(receptions, 1, 2, 'same')
relation(receptions, 1, 3, 'unknown', 'shift-equality-unproved')
r = inspect(receptions)
assert r['uses'][0]['compatibility'] == {
    'relation': 'unknown', 'reasons': ['reception-has-no-trusted-domain']}
received = [v for v in r['values'] if 'authored_sender_value' in v]
assert len(received) == 4
assert all(v['domain'] is None and not v['may_depend_on'] for v in received)
# Repeated authored output names in separate invocations never equate values.
assert len([v for v in r['values'] if v['name'] == 'v']) == 4

# Separate receptions of size also remain unknown with the exact same shift.
separate_size = receptions.replace('message second:P(s)->V(s2);',
    'message second:P(s)->V(s2); message size2:P(n)->V(n2);')
separate_size = separate_size.replace('Points(s2,n1)', 'Points(s1,n2)')
relation(separate_size, 1, 3, 'unknown', 'size-equality-unproved')

# Multilinear data gets no multiplicative coset by field, shape or name.
multilinear = '''module {
  bind fold=poly::fold(bls12-381.fr);
  fn Work(t:Table<"bls12-381.fr">,s:"bls12-381.fr"::Element)->(Table<"bls12-381.fr">) {
    let next = fold(t,s); return(next);
  }
  protocol Main {roles(P); inputs(P t:Table<"bls12-381.fr">,P s:"bls12-381.fr"::Element);
    local P:let v = Work(t,s); return();}
  instance main_instance:Main {roles(P=P);} entry main=main_instance;
}'''
m = inspect(multilinear)
assert not m['domains'] and not m['uses']
assert next(v for v in m['values'] if v['name'] == 'next')['unknown_reason'] == \
    'no-installed-domain-transfer'

# An arbitrary word can be interpreted repeatedly on the same coset without
# inheriting a low-degree or producer fact. The different interpretation is legal.
arbitrary = source.replace('let v = poly::coset_evaluate::<F>(p,s,n);',
    'let v = poly::coefficients::<F>(p);')
a = inspect(arbitrary)
assert a['uses'][0]['compatibility']['reasons'] == ['no-producer-domain-fact']
assert a['domains'][0]['size_origin_is_length']
assert a['terms'][a['domains'][0]['size']]['kind'] == 'length'

# Finite loop occurrences retain distinct reception leaves even when authored
# names and sender provenance are identical on each iteration.
loop = receptions.replace('    local V:let a = Points(s1,n1);', '''
    loop [repeated] 2 carry () capture(s,n1) -> () {
      message again:P(s)->V(fresh);
      local V:let word = Points(fresh,n1);
      yield();
    }
    local V:let a = Points(s1,n1);''')
relation(loop, 1, 2, 'unknown', 'shift-equality-unproved')

# Admission is mandatory. A missing algebraic requirement cannot be converted
# into an optimistic fact, even if a closed selection happens to be odd.
missing = source.replace(',CharacteristicNotTwo(F)', '')
run('domain-inspect', missing, 'main', refuses='generic-public-requirement')
run('domain-inspect', source.replace('koala-bear', 'bls12-381.fr'),
    'main', refuses='source-protocol-requirement')
run('domain-inspect', source, 'absent', refuses='execution-entry')
run('domain-inspect', source, 'main', '--compare=x,1', refuses='unsupported-option')
relation(source, 0, 1000, 'unknown', 'domain-id-out-of-range')

print(f'{commands.save()} polynomial domain inspection checks passed')

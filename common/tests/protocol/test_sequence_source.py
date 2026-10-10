"""Contextual source products cross ordinary native sequence and codec boundaries."""
from pathlib import Path

import pytest

from entry import Entry
from journal import names

ROOT = Path(__file__).resolve().parents[3]
MODULES = [f'--module=zkc::sequence={ROOT}/libraries/zkc/sequence.zkc']


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_source_sequence_products(toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::sequence::{Sequence,empty,append,length,get};
domain F=field("bls12-381.fr");
struct Pair<T:Type>{pub first:T,pub second:T}
struct Entry<D:Field>{pub weight:D,pub nested:Pair<D>,pub array:[(D,bool);2]}
struct Empty{}
enum Choice{Some(F),None()}
fn single<T:Type+Copy+Drop>(x:T)->Sequence<T>{return append(empty<T>(),x);}
fn array_roundtrip<T:Type+Copy+Drop,N:nat>(x:[T;N])->[T;N]{return get(single(x),0);}
fn produce(a:F,b:F)->Sequence<Sequence<Entry<F>>>{
  let item=Entry<F>{weight:a,nested:Pair<F>{first:a,second:b},array:[(a,true),(b,false)]};
  return single(single(item));
}
fn inspect(xs:Sequence<Sequence<Entry<F>>>,i:index)->(F,F,F,[F;2],(F,F),Choice,index){
  let item=get(get(xs,0),i);
  let pair=get(single((item.nested.first,item.nested.second)),0);
  let unit=get(single(()),0);
  let stored_empty=get(single(Empty{}),0);
  let array=array_roundtrip([pair.0,pair.1]);
  let choice=get(single(Choice::Some(item.weight)),0);
  return (item.weight,item.array[0].0,item.array[1].0,array,pair,choice,length(get(xs,0)));
}
protocol Run roles(P,V)(a:F@P,b:F@P,i:index@V)
 ->(xs:Sequence<Sequence<Entry<F>>>@V,r:(F,F,F,[F;2],(F,F),Choice,index)@V){
  let xs @P =produce(a,b);let ys=send P->V(xs);
  let r @V =inspect(ys,i);return(xs=ys,r=r);
}run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    result = entry.run_roles('valid', {'P': {'inputs': {'a': '7', 'b': '19'}},
                                      'V': {'inputs': {'i': '0'}}})['V']
    assert result['r'][:5] == ['7', '7', '19', ['7', '19'], ['7', '19']]
    assert result['r'][5] == {'case': 'Some', 'fields': {'0': '7'}}
    assert result['r'][6] == '1'
    refused = entry.run_roles('bounds', {'P': {'inputs': {'a': '7', 'b': '19'}},
                               'V': {'inputs': {'i': '1'}}}, refuses='entry-run-incomplete')
    assert names(str(refused), 'sequence-index')
    # Returned native JSON feeds a separately compiled source Entry, preserving
    # every nested nominal carrier through decode, sequence.at and encode.
    replay_source = source[:source.index('protocol Run')] + '''
protocol Run roles(P)(xs:Sequence<Sequence<Entry<F>>>@P,i:index@P)
 ->(xs:Sequence<Sequence<Entry<F>>>@P,r:(F,F,F,[F;2],(F,F),Choice,index)@P){
  let r @P =inspect(xs,i);return(xs=xs,r=r);
}run Demo=Run;
'''
    replay_dir = directory / 'replay'
    replay_dir.mkdir()
    replay = Entry(toolchain, journal, replay_dir, replay_source, [*MODULES, *flags])
    assert replay.run('codec', {'xs': result['xs'], 'i': '0'}) == result

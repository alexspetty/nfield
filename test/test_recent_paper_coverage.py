"""Fail when the reviewed seven-work computational correspondence drifts.

This gate checks inventory, source inclusion, linked API symbols, command
registration and mathematical-scope declarations. The independent arithmetic
tests are separate default targets. It does not interpret a status string or
a successful build as a proof of an infinite theorem.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]
EXPECTED={
    'the_structure_that_survives':17,
    'carry_boundaries_and_bernoulli_spectra':23,
    'additive_boundaries_and_conductor_energies_of_periodic_remainder_orbits':21,
    'the_cubic_law_for_digit_collision_energy':18,
    'the_secondary_term_in_digit_collision_energy':22,
    'the_stationary_to_diagonal_transition_in_collision_capacity':22,
    'finite_generation_of_collision_capacity':20,
}
data=json.loads((ROOT/'coverage/recent_papers.json').read_text())
assert data['schema']==1
assert {p['key']:len(p['families']) for p in data['papers']}==EXPECTED
assert len(data['papers'])==len(EXPECTED)
commands=set(subprocess.check_output([str(ROOT/'nfield'),'__complete'],text=True).splitlines())
verifiers=set(subprocess.check_output([str(ROOT/'nfield'),'__complete','verify'],text=True).splitlines())
symbols=subprocess.check_output(['nm','-g','--defined-only',str(ROOT/'libnfield.a')],text=True)
symbols={line.split()[-1] for line in symbols.splitlines() if len(line.split())>=3}
makefile=(ROOT/'Makefile').read_text()
for obj in data['objects'].values():
    assert obj['command'] in commands and obj['command'] in verifiers,obj['command']
    assert obj['domain'] and obj['functions'] and obj['validation'],obj
    for rel in obj['sources']:
        assert (ROOT/rel).is_file(),rel
        if rel.endswith('.c'):assert rel in makefile,rel
    for symbol in obj['functions']:assert symbol in symbols,symbol
    help_text=subprocess.check_output([str(ROOT/'nfield'),'help',obj['command']],text=True)
    assert help_text.strip(),obj['command']
paper_root=Path(os.environ.get('NFIELD_PAPER_ROOT',str(ROOT.parent)))
checked_sources=0
for paper in data['papers']:
    assert paper['expected_family_count']==EXPECTED[paper['key']]
    assert [f['id'] for f in paper['families']]==[str(n) for n in range(1,len(paper['families'])+1)]
    assert paper['labels'] and paper['result_environment_count']>0
    for family in paper['families']:
        assert family['name'] and family['location'] and family['proof_boundary'],family
        assert family['computational_status']=='implemented_with_declared_limits',family
        assert family['objects'] and set(family['objects'])<=data['objects'].keys(),family
    source=paper_root/paper['manuscript']
    if source.exists():
        raw=source.read_bytes()
        assert hashlib.sha256(raw).hexdigest()==paper['sha256'],str(source)+' needs reconciliation'
        text=re.sub(r'(?<!\\)%[^\n]*','',raw.decode())
        assert re.findall(r'\\label\{([^}]+)\}',text)==paper['labels'],str(source)
        count=len(re.findall(r'\\begin\{(?:theorem|lemma|proposition|corollary|remark)\}',text))
        assert count==paper['result_environment_count'],str(source)
        checked_sources+=1
if os.environ.get('NFIELD_REQUIRE_PAPERS')=='1':assert checked_sources==7,checked_sources
for target in ('test-capacity-resolution','test-capacity-generation','test-recent-paper-computations',
               'test-recent-paper-transport','test-recent-paper-coverage'):
    default=re.search(r'^test:(.*)$',makefile,re.M).group(1).split()
    assert target in default,target
print(json.dumps({'passed':True,'papers':7,'families':sum(EXPECTED.values()),
                  'object_mappings':len(data['objects']),'manuscript_hashes_checked':checked_sources,
                  'boundary':'Local declared computational ranges only; no Lean or public-release certification.'}))

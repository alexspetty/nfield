"""Integrity gate for the reviewed published computational counterparts.

Counts do not replace arithmetic tests. Frozen code hashes require explicit
review when implementations change. Optional manuscript checks pin versions;
public distributions report them as unavailable rather than claiming a read.
"""
import hashlib,json,os,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
data=json.loads((ROOT/'coverage/published_extensions.json').read_text())
assert data['schema']==1 and data['counts']==dict(results=84,displays=607,worked_problems=44,open_problems=1)
for path,digest in data['source_sha256'].items():assert sha(ROOT/path)==digest,(path,'reviewed implementation changed')
counts={k:0 for k in data['counts']};sources=0
for p in data['papers']:
 for key in ('results','displays','problems'):
  for row in p[key]:
   assert row['objects'] and set(row['objects'])<=data['objects'].keys()
   assert re.fullmatch('[0-9a-f]{64}',row['statement_sha256'])
 if p['key']=='unity_refinement':assert len(p['results'])==27 and len(p['displays'])==172
 if p['key']=='unit_sampling':assert len(p['results'])==18 and len(p['displays'])==105
 if p['key']=='collision_calculus':assert len(p['results'])==39 and len(p['displays'])==330
 counts['results']+=len(p['results']);counts['displays']+=len(p['displays'])
 counts['open_problems']+=sum(x['status']=='open_research_problem' for x in p['problems'])
 counts['worked_problems']+=sum(x['status']=='worked_question_with_finite_counterparts' for x in p['problems'])
 manuscript=ROOT.parent/p['source']
 if manuscript.is_file():assert sha(manuscript)==p['source_sha256'];sources+=1
assert counts==data['counts']
if os.environ.get('NFIELD_REQUIRE_PAPERS')=='1':assert sources==3
commands=set(subprocess.check_output([str(ROOT/'nfield'),'__complete'],text=True).split())
for name,o in data['objects'].items():
 assert o['command'] in commands and o['domain'] and o['proof_boundary'] and o['independent_tests'],name
 candidates=set(subprocess.check_output([str(ROOT/'nfield'),'__complete',o['command']],text=True).split())
 assert set(o['actions'])<=candidates,(name,set(o['actions'])-candidates)
 helptext=subprocess.check_output([str(ROOT/'nfield'),'help',o['command']],text=True)
 for action in o['actions']:assert action in helptext,(name,action)
 for option in o.get('options',[]):assert option in candidates and option in helptext,(name,option)
 for rel in o['sources']+o['independent_tests']:assert rel in data['source_sha256'],rel
print(json.dumps(dict(passed=True,**counts,manuscript_hashes_checked=sources,boundary='Finite counterparts within declared limits; open and analytic clauses remain separate.')))

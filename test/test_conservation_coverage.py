"""Validate the frozen computational map without requiring private proof files."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
d=json.loads((root/'coverage/conservation.json').read_text())
assert d['schema']==1 and len(d['objects'])==33 and len(d['rows'])==149
used=set()
for row in d['rows']:
 assert row['computational_status']=='complete' and row['objects']
 assert set(row['objects'])<=d['objects'].keys();used.update(row['objects'])
assert used==d['objects'].keys()
for name,o in d['objects'].items():
 assert o['sources'] and o['interfaces'] and o['checked_oracles'] and o['admitted_domain'],name
 for oracle in o['checked_oracles']:assert oracle['checks']>0 and oracle['independence'] and oracle['domain']
for rel,expected in d['source_sha256'].items():assert hashlib.sha256((root/rel).read_bytes()).hexdigest()==expected,(rel,'reviewed Conservation implementation changed')
print('PASS portable Conservation computational map: 149 rows, 33 objects; source and included oracle hashes checked. Formal bundle remains separate.')

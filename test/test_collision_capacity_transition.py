#!/usr/bin/env python3
"""Focused CLI and JSON/TCP tests for the transition paper's native interface."""
import csv
import io
import json
from pathlib import Path
import socket
import subprocess
import tempfile
import time

ROOT=Path(__file__).resolve().parents[1]
BIN=str(ROOT/'nfield')
checks=[]
def run(*args,ok=True):
    p=subprocess.run([BIN,*args],capture_output=True,text=True,timeout=45)
    assert (p.returncode==0)==ok,(args,p.returncode,p.stdout,p.stderr)
    checks.append({'args':args,'exit_code':p.returncode})
    return p.stdout
def data(*args): return list(csv.DictReader(io.StringIO(run('capacity-resolution',*args))))

assert 'capacity-resolution' in run('__complete').splitlines()
assert 'capacity-resolution' in run('commands')
assert 'capacity-resolution' in run('__complete','help').splitlines()
assert 'capacity-resolution' in run('__complete','verify').splitlines()
actions=run('__complete','capacity-resolution').splitlines()
for a in ['constants','inspect','window','sample','unit','spectrum','progression','verify']: assert a in actions
assert 'Prime observations use continuous capacity' in run('help','capacity-resolution')
assert '0 failures' in run('verify','capacity-resolution')
r=data('inspect','1')[0]; assert abs(float(r['J'])-1/3)<1e-14 and float(r['y'])==0
r=data('inspect','17','60')[0]; assert r['M']=='60' and r['n']=='17'
w=data('window','100'); assert w[0]['count']=='100' and w[1]['count']=='20'
s=data('sample','100','20','7'); assert len(s)==7 and s[0]['n']=='101' and s[-1]['n']=='200'
u=data('unit','6')[0]; assert abs(float(u['unit_mean'])+float(u['mass'])/3)<1e-14
sp=data('spectrum','120','60'); cutoff=float(data('inspect','120','60')[0]['Y_M'])
assert abs(sum(float(r['contribution']) for r in sp)-cutoff)<1e-14
assert sp[0]['endpoint']=='negative'
pr=data('progression','1000','30','29')[0]; assert pr['count']=='33'
constants=data('constants'); assert len(constants)==7 and float(constants[3]['value'])<0
for args in [('inspect','0'),('inspect','12junk'),('inspect','2000001'),('window','1000001'),
             ('sample','20','30','1'),('sample','1000000','1000000','5000'),('unit','61'),
             ('spectrum','0','2001'),('progression','100','11','0'),('progression','100','6','6'),
             ('constants','extra'),('bogus',)]:
    run('capacity-resolution',*args,ok=False)

with tempfile.TemporaryFile(mode='w+') as log:
    with socket.socket() as s: s.bind(('127.0.0.1',0));port=s.getsockname()[1]
    proc=subprocess.Popen([BIN,'daemon','--port',str(port),'--threads','1'],stdout=log,stderr=log)
    try:
        for _ in range(100):
            try:
                conn=socket.create_connection(('127.0.0.1',port),timeout=.5);conn.close();break
            except OSError: time.sleep(.05)
        for command,expected in [('capacity-resolution inspect 17 12','B2_correction'),
                                 ('capacity-resolution window 100','prime_predecessors'),
                                 ('verify capacity-resolution','0 failures')]:
            with socket.create_connection(('127.0.0.1',port),timeout=30) as conn:
                conn.sendall((json.dumps({'cmd':command})+'\n').encode())
                raw=conn.makefile('r').readline(); response=json.loads(raw)
                assert expected in raw,(command,response)
                checks.append({'api_command':command,'json_valid':True,'expected_output':expected})
    finally:
        proc.terminate();proc.wait(timeout=10)
print(json.dumps({'interface_checks':len(checks),'passed':True,'checks':checks},indent=2))

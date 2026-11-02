#!/usr/bin/env python3
"""Independent primitive-row and multiple-inverse correspondence checks.

Proper-divisor subtraction builds reference rows; literal complete periods
give their cross products. Direct additive exponentials check Ramanujan and
DFT identities. Back substitution recovers finite masses without Mobius.
Infinite inverse containment comes from Lean, not these finite comparisons.
"""
import argparse
import cmath
from fractions import Fraction as F
from math import gcd, lcm, pi, sin, tan
from pathlib import Path
import subprocess
import sys

parser=argparse.ArgumentParser()
parser.add_argument('--driver',required=True)
parser.add_argument('--bin')
args=parser.parse_args()
checks=cli_cases=0
maximum=0.0

def check(condition,context):
    global checks
    checks+=1
    assert condition,context

def close(actual,expected,q,context):
    global maximum
    error=abs(actual-expected)/(1+q)
    maximum=max(maximum,error)
    check(error<=5e-12,(context,actual,expected,error))

P={1:[F(0)]};R={1:[F(0)]};C={1:[F(1)]}
for q in range(2,241):
    ds=[d for d in range(1,q) if q%d==0]
    P[q]=[F(2*a-q+1,2)-sum((P[d][a%d] for d in ds),F(0)) for a in range(q)]
    R[q]=[(F(2*a-q,2) if a else F(0))-sum((R[d][a%d] for d in ds),F(0)) for a in range(q)]
    C[q]=[F(q if a==0 else 0)-sum((C[d][a%d] for d in ds),F(0)) for a in range(q)]
norms={q:[sum((x*x for x in row),F(0))/q for row in (P[q],R[q],C[q])]
       for q in range(2,241)}
mu=[0,1]+[0]*239
for n in range(2,241):mu[n]=-sum(mu[d] for d in range(1,n) if n%d==0)
collision=[F(0)]*241;H=F(0)
for k in range(2,241):
    H+=F(1,k-1)
    collision[k]=(k*H-sum((d**3*collision[d] for d in range(2,k) if k%d==0),F(0)))/k**3
prefix=[sum(collision[:m+1],F(0)) for m in range(241)]
amplitudes={m:[sum((collision[k] for k in range(q,m+1,q)),F(0)) for q in range(2,241)]
            for m in range(2,241)}

run=subprocess.run([str(Path(args.driver).resolve())],text=True,capture_output=True)
if run.returncode:
    print(run.stderr,file=sys.stderr);raise SystemExit(run.returncode)
profiles={};inputs={};xis={};rows={};observations=[];records=references=edges=0
for line in run.stdout.splitlines():
    p=line.split();kind=p[0]
    if kind=='row':
        q,n,res,rad,scale,phi,j2=map(int,p[1:8]);values=list(map(F,p[8:]))
        a=n%q
        expected_rad=1
        for t in range(2,q+1):
            if q%t==0 and all(t%d for d in range(2,t)):expected_rad*=t
        check((res,rad,scale)==(a,expected_rad,q//expected_rad),line)
        check((phi,j2)==(int(norms[q][2]),int(12*norms[q][0])),line)
        expected=[P[q][a],R[q][a],C[q][a],*norms[q],scale*P[rad][(n//scale)%rad]]
        check(values==expected,line)
        if 0<=n<q:rows[q,n]=values[:3]
        records+=1
    elif kind=='profile':
        ident,M,raw=map(int,p[1:]);profiles[ident]=(M,raw);inputs[ident]={};xis[ident]={}
    elif kind=='input':inputs[int(p[1])][int(p[2])]=F(p[3])
    elif kind=='amplitude':xis[int(p[1])][int(p[2])]=F(p[3]);records+=1
    elif kind in ('inverse','inverse_alias'):observations.append(p);records+=1
    elif kind=='reference':
        q,d,L=map(int,p[1:4]);pp,rr,cc,pr,pc,rc=map(int,p[4:])
        check(L==lcm(q,d),line)
        if q==d:
            check([F(pp,4*L),F(rr,4*L),F(cc,L),F(pr,4*L),F(pc,2*L),F(rc,2*L)]==
                  [*norms[q],norms[q][1],-norms[q][2]/2,0],line)
        else:check((pp,rr,cc,pr,pc,rc)==(0,0,0,0,0,0),line)
        references+=1
    elif kind=='recovery':
        d,Q,M,J,bd,bj=map(int,p[1:7]);bl,bu,E,lo,hi=map(F,p[7:])
        check(J==Q//d and 2**(bd-1)<2*d<=2**bd and 2**(bj-1)<2*J<=2**bj,line)
        finite=sum((mu[j]*amplitudes[M][d*j-2] for j in range(1,J+1)),F(0))
        low=finite-sum(mu[j]<0 for j in range(1,J+1))*(1-prefix[M])
        high=finite+sum(mu[j]>0 for j in range(1,J+1))*(1-prefix[M])
        error=F(4*(bd+2*bj+3),d*d*J)
        check((bl,bu,E,lo,hi)==(low,high,error,max(F(0),low-error),high+error),line)
        check(lo<=collision[d]<=hi,line)
        # Later positive amplitude partial sums check the raw prefix interval.
        later=sum((mu[j]*amplitudes[240][d*j-2] for j in range(1,J+1)),F(0))
        check(bl<=later<=bu,line)
        records+=1
    elif kind=='edges':
        edges=int(p[1]);check(int(p[3])==len(profiles),line)
    else:raise AssertionError(line)

recovered={}
for ident,(M,raw) in profiles.items():
    # Descending subtraction of already recovered higher multiples; no mu.
    result={}
    for k in range(M,1,-1):
        result[k]=xis[ident][k]-sum((result[j] for j in range(2*k,M+1,k)),F(0))
    recovered[ident]=result
    if not raw:check(result==inputs[ident],('profile recovery',ident))
    else:check(xis[ident]==inputs[ident],('raw amplitudes',ident))
    for k in range(2,M+1):
        check(xis[ident][k]==sum((result[j] for j in range(k,M+1,k)),F(0)),(ident,k))
for p in observations:
    ident=int(p[1]);k=int(p[2]) if p[0]=='inverse' else 2
    check(F(p[-1])==recovered[ident].get(k,F(0)),p)

for ident,(M,_) in profiles.items():
    v=recovered[ident]
    for n in [-13,-1,0,1,6,120,10**80]:
        # Actual production amplitudes and primitive rows reconstruct the
        # independent raw remainder potential and its odd/even split.
        primitive=sum((xis[ident][q]*rows[q,n%q][0] for q in range(2,M+1)),F(0))*F(2,3)
        carrier=sum((xis[ident][q]*rows[q,n%q][1] for q in range(2,M+1)),F(0))*F(2,3)
        ramanujan=sum((xis[ident][q]*rows[q,n%q][2] for q in range(2,M+1)),F(0))*F(-2,3)
        centered=sum((v[k]*F(2*(n%k)-k+1,3) for k in v),F(0))
        increment=F(2,3)*(sum(v.values(),F(0))-sum((k*v[k] for k in v if n%k==0),F(0)))
        check(primitive==centered and ramanujan==increment and primitive==carrier+increment/2,
              ('finite conductor reconstruction',ident,n))

check(P[6]==list(map(F,[-1,-2,-1,1,2,1])),'published P6 fixture')
check(len(rows)==sum(range(2,241)),'complete production row table')
for q in range(2,241):
    units=[a for a in range(1,q) if gcd(a,q)==1]
    # Root phases are built directly, independent of integer divisor formulas.
    roots=[cmath.exp(2j*pi*a/q) for a in range(q)]
    for n in range(q):
        ram=sum(roots[(a*n)%q] for a in units)
        close(ram,complex(rows[q,n][2]),q,('Ramanujan exponential',q,n))
        check(rows[q,n][0]==rows[q,n][1]-rows[q,n][2]/2,('split',q,n))
        check(rows[q,n][1]==-rows[q,(-n)%q][1],('odd reflection',q,n))
    total=0.0
    for a in range(q):
        transforms=[sum(float(rows[q,n][i])*roots[(-a*n)%q] for n in range(q))/q for i in range(3)]
        if a in units:
            expected=[complex(-0.5,0.5/tan(pi*a/q)),complex(0,0.5/tan(pi*a/q)),1]
            total+=1/sin(pi*a/q)**2
        else:expected=[0,0,0]
        for i in range(3):close(transforms[i],expected[i],q,('DFT',q,a,i))
    close(total,float(4*norms[q][0]),q,('primitive cosecant square',q))

if args.bin:
    binary=str(Path(args.bin).resolve())
    def cli(words,ok=True):
        global cli_cases
        cli_cases+=1
        r=subprocess.run([binary,'weighted-remainder-state',*map(str,words)],capture_output=True,text=True)
        check((r.returncode==0)==ok,(words,r.returncode,r.stdout,r.stderr))
        return r.stdout
    def fields(s):return dict(line.split('=',1) for line in s.splitlines() if '=' in line)
    for q in range(2,241):
        output=cli(['rows',q]);f=fields(output)
        check(F(f['primitive_norm_squared'])==norms[q][0],q)
        check(F(f['odd_norm_squared'])==norms[q][1],q)
        check(F(f['ramanujan_norm_squared'])==norms[q][2],q)
        lines=[line.split() for line in output.splitlines() if line.startswith('row ')]
        check(len(lines)==q,q)
        for a,line in enumerate(lines):
            check(int(line[1])==a and list(map(F,line[2:]))==[P[q][a],R[q][a],C[q][a],P[q][a]],line)
    for q in [2,4,6,12,30,72,120,239,240]:
        for n in [-1,-13,-10**80,10**80]:
            output=cli(['rows',q,n]);line=next(x.split() for x in output.splitlines() if x.startswith('row '))
            check(list(map(F,line[2:]))==[P[q][n%q],R[q][n%q],C[q][n%q],P[q][n%q]],(q,n))
    for ident,(M,_) in profiles.items():
        terms=[f'{q}:{v}' for q,v in xis[ident].items() if v]
        for k in sorted({2,M,240}):
            f=fields(cli(['mass-inverse',M,k,*terms]));check(F(f['recovered_mass'])==recovered[ident].get(k,F(0)),(ident,k))
    for d,Q,M in [(2,2,2),(2,240,240),(6,12,24),(120,239,2),(240,240,240)]:
        f=fields(cli(['mass-recovery',d,Q,M]))
        check(F(f['mass_lower'])<=collision[d]<=F(f['mass_upper']),(d,Q,M))
    bad=[[],['rows'],['rows',1],['rows',241],['rows',2,'+1'],['rows',2,'-'],['rows',2,'1/2'],
         ['rows',2,'1 2'],['rows',2,1,2],['mass-inverse'],['mass-inverse',1,2],['mass-inverse',2,1],
         ['mass-inverse',2,2,'3:1'],['mass-inverse',2,2,'2:1','2:1'],['mass-inverse',2,2,'2:1/0'],
         ['mass-inverse',2,2,'2:1/-2'],['mass-inverse',2,2,'2:'],['mass-inverse',2,2,':1'],
         ['mass-inverse',2,2,'2:1:1'],['mass-inverse',2,2,'2:1.0'],['mass-inverse',2,2,'0:1'],
         ['mass-recovery',3,2,240],['mass-recovery',2,2,241],['mass-recovery',2,2,1],
         ['mass-recovery',2,2,2,2],['mass-recovery',2,2]]
    # Bare family command has its own successful help contract.
    for words in bad[1:]:cli(words,False)
print(f'PASS: {checks+edges} checks; {len(profiles)} profiles; {records} API records; '
      f'{references} literal complete-period pair references; {edges} C edge assertions; '
      f'{cli_cases} CLI cases; max scaled complex error {maximum:.3e} (tolerance 5e-12).')

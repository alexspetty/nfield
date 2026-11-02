#!/usr/bin/env python3
"""Independent reset-event cycles and finite-increment correlations."""
import argparse
from fractions import Fraction as F
from math import lcm
from pathlib import Path
import subprocess
import sys

parser=argparse.ArgumentParser();parser.add_argument('--driver',required=True);parser.add_argument('--bin')
args=parser.parse_args();checks=cli_cases=0
def check(x,context):
    global checks
    checks+=1;assert x,context

run=subprocess.run([str(Path(args.driver).resolve())],capture_output=True,text=True)
if run.returncode:
    print(run.stderr,file=sys.stderr);raise SystemExit(run.returncode)
profiles={};weights={};shifts={};references={};observations=[];states=[];aliases=[];edges=0;records=0
for line in run.stdout.splitlines():
    p=line.split()
    if p[0]=='profile':
        ident,M,kind=map(int,p[1:]);profiles[ident]=(M,kind);weights[ident]={}
    elif p[0]=='weight':weights[int(p[1])][int(p[2])]=F(p[3])
    elif p[0]=='shift':shifts[int(p[1])]=int(p[2])
    elif p[0]=='reference':
        s,k,l,L,hits=map(int,p[1:]);check(L==lcm(k,l) and (k*l)%L==0,line)
        references[s,k,l]=(k*l//L)*hits-1
    elif p[0]=='state':states.append(p);records+=1
    elif p[0]=='state_alias':aliases.append(p);records+=1
    elif p[0]=='edges':edges=int(p[1]);check(int(p[3])==len(profiles),line)
    else:observations.append(p);records+=1

collision=[F(0)]*241;H=F(0)
for k in range(2,241):
    H+=F(1,k-1)
    collision[k]=(k*H-sum((d**3*collision[d] for d in range(2,k) if k%d==0),F(0)))/k**3

def scaled_products(v):
    den=lcm(*(value.denominator for value in v.values()))
    values={k:int(v[k]*den) for k in v}
    return den,[(k,l,values[k]*values[l]*(1 if k==l else 2)) for k in values for l in values if l<=k]

def covariance_reference(v,h):
    den,products=scaled_products(v);total=0
    for k,l,product in products:
        # Independent literal joint-reset visits over the full period.
        L=lcm(k,l)
        hits=sum((a+h)%l==0 for a in range(0,L,k))
        total+=product*((k*l//L)*hits-1)
    return F(4*total,9*den*den)

answers={}
for ident,(M,kind) in profiles.items():
    v=weights[ident]
    if kind==0:check(v=={k:collision[k] for k in range(2,M+1)},('collision weights',ident))
    den,products=scaled_products(v)
    for s,h in shifts.items():
        answers[ident,s]=F(4*sum(product*references[s,k,l] for k,l,product in products),9*den*den)
    period=lcm(*v)
    if period<=60000:
        # Build centered ages, then their literal backward differences.
        scale=3*den
        ages=[sum(int(v[k]*den)*(2*(n%k)-k+1) for k in v) for n in range(period)]
        increments=[ages[n]-ages[n-1] for n in range(period)]
        check(sum(increments)==0,('finite mean',ident))
        for s,h in shifts.items():
            direct=F(sum(increments[n]*increments[(n+h)%period] for n in range(period)),period*scale*scale)
            check(direct==answers[ident,s],('whole-cycle increment',ident,s))
    check(answers[ident,0]>=0 and answers[ident,1]==answers[ident,2],('variance/evenness',ident))
for p in observations:
    ident=int(p[1])
    if p[0]=='finite':
        s=int(p[2]);a,r,z,o=map(F,p[3:]);check((a,r,z,o)==(answers[ident,s],answers[ident,s],answers[ident,0],answers[ident,1]),p)
    elif p[0] in ('weight_alias','shift_alias'):
        check(F(p[2])==covariance_reference(weights[ident],-13),p)
    else:raise AssertionError(p)

# Collision reference arrays are computed once for all cutoffs, using the
# literal event-count kernels above. One common denominator avoids repeated
# normalization inside the independent double sums.
den=lcm(*(x.denominator for x in collision))
scaled=[int(x*den) for x in collision];prefix={s:[F(0)]*241 for s in shifts}
for s in shifts:
    total=0
    for M in range(2,241):
        total+=sum(scaled[M]*scaled[l]*(1 if M==l else 2)*references[s,M,l] for l in range(2,M+1))
        prefix[s][M]=F(4*total,9*den*den)
by_shift={h:s for s,h in shifts.items()};lcm_cutoff=1;periods={}
for M in range(2,241):lcm_cutoff=lcm(lcm_cutoff,M);periods[M]=lcm_cutoff
state_values={}
for p in states:
    M,b,h,L=map(int,p[1:5]);mass,a,r,z,o,E,Eg,u,error,lo,hi,pr,cr=map(F,p[5:])
    expected=prefix[0][M] if h==L else prefix[by_shift[h]][M]
    check(L==periods[M] and 2**(b-1)<2*M<=2**b,p)
    check((mass,a,r,z,o)==(sum(collision[:M+1],F(0)),expected,expected,prefix[0][M],prefix[1][M]),p)
    check(E==F(256*(b+1)**2,M) and Eg==4*E and pr==4*E and cr==8*E,p)
    check(u>=0 and u*u>=z*Eg and (u-F(1,M*M))**2<z*Eg,p)
    check((error,lo,hi)==(2*u+Eg,a-(2*u+Eg),a+(2*u+Eg)),p)
    check(z>0 and o<0,p)
    # Later finite covariance values supplement the actual Lean enclosure.
    if h in by_shift:check(lo<=prefix[by_shift[h]][240]<=hi,p)
    state_values[M,h]=(a,r,z,o,E,Eg,u,error,lo,hi,pr,cr)
for p in aliases:
    M,h=map(int,p[1:3]);check(F(p[3])==covariance_reference({k:collision[k] for k in range(2,M+1)},h),p)

if args.bin:
    binary=str(Path(args.bin).resolve())
    def cli(words,ok=True):
        global cli_cases
        cli_cases+=1;r=subprocess.run([binary,'weighted-remainder-state',*map(str,words)],capture_output=True,text=True)
        check((r.returncode==0)==ok,(words,r.returncode,r.stdout,r.stderr))
        return dict(line.split('=',1) for line in r.stdout.splitlines() if '=' in line)
    keys=['finite_arithmetic','finite_ramanujan','finite_zero','finite_one','potential_squared_error',
          'increment_squared_error','cross_upper','covariance_error','full_lower','full_upper',
          'potential_recurrence_squared_upper','covariance_recurrence_loss_upper']
    for M in range(2,241):
        f=cli(['increment-recurrence',M]);check(int(f['shift'])==int(f['cutoff_period'])==periods[M],M)
        check(tuple(F(f[k]) for k in keys)==state_values[M,periods[M]],M)
        check(f['finite_return_equals_zero']=='1' and f['finite_zero_positive']=='1' and f['finite_one_negative']=='1',M)
    for M in [2,3,6,12,31,60,120,239,240]:
        for h in shifts.values():
            f=cli(['increment-covariance',M,h]);check(tuple(F(f[k]) for k in keys)==state_values[M,h],(M,h))
    for words in [['increment-covariance'],['increment-covariance',2],['increment-covariance',1,0],
                  ['increment-covariance',241,0],['increment-covariance',2,'1/2'],['increment-covariance',2,'+1'],
                  ['increment-covariance',2,'-'],['increment-covariance',2,'1 2'],['increment-covariance',2,0,1],
                  ['increment-recurrence'],['increment-recurrence',0],['increment-recurrence',1],
                  ['increment-recurrence',241],['increment-recurrence',2,1]]:cli(words,False)
print(f'PASS: {checks+edges} checks; {len(profiles)} profiles; {records} API records; '
      f'{len(references)} complete-cycle reset-pair references; {edges} C edge assertions; {cli_cases} CLI cases.')

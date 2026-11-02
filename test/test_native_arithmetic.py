#!/usr/bin/env python3
"""Independent floors, family superposition and complete packet reference."""
import argparse
from fractions import Fraction as F
from decimal import Decimal as D
from math import gcd
from pathlib import Path
import json
import re
import subprocess
import test_native_detector as ref

checks=0


def check(value,label):
    global checks
    checks+=1
    assert value,label


def mu(n):
    factors=0
    for p in range(2,n+1):
        if n%p==0:
            n//=p;factors+=1
            if n%p==0:return 0
    return (-1)**factors


def coeff(S,r):
    def profile(j):
        shape=F(1,r) if r<=j<2*r else -F(1,r) if 2*r<=j<4*r else F(1,4*r) if 4*r<=j<8*r else F(0)
        return shape*min(1,max(F(0),F(2*S-j,S)))
    return [F(0)]+[j*(profile(j)-profile(j-1)) for j in range(1,2*S+1)]


def field(c,n):
    return sum((v*F(n%j,j) for j,v in enumerate(c) if j),F(0))


def families(S):
    rows=[coeff(S,r) for r in range(1,2*S,2)]
    return [sum((mu(r)*rows[(r-1)//2][j] for r in range(1,2*S,2)),F(0)) for j in range(2*S+1)]


def packet(t):
    # Classical block averages, rather than differentiating the tapered
    # Mertens profile as the C implementation does.
    def precursor(s):
        result=[F(0) for _ in range(2*s+1)]
        for n in range(s+1,2*s+1):
            A=sum((F(mu(j),j) for j in range(1,n+1)),F(0))
            for j in range(2,n+1):result[j]-=F(mu(j),s)
            result[n]+=n*A/s
        return result
    result=[F(0) for _ in range(8*t+1)]
    for s,a,w in ((2*t,2,3),(t,4,-2),(4*t,1,-1)):
        for j,c in enumerate(precursor(s)):
            if j<2:continue
            result[a*j]+=w*c
            if a>1:result[a]-=w*c/j
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--bin',required=True)
    binary=str(Path(parser.parse_args().bin).resolve())
    def run(*args,fail=False,timeout=60):
        p=subprocess.run([binary,'native-refinement',*map(str,args)],capture_output=True,text=True,timeout=timeout)
        check((p.returncode!=0)==fail,(args,p.stdout,p.stderr))
        if fail:check(not p.stdout,('failed command emitted data',args));return
        if '--json' in args:return json.loads(p.stdout)
        data={}
        for line in p.stdout.splitlines():
            if '=' in line and ' ' not in line:
                k,v=line.split('=',1)
                try:data[k]=F(v)
                except ValueError:pass
        return data,p.stdout
    for j,n,bases in ((7,3,[2,3,5]),(5,10,[10]),(13,4,[36]*16),(11,0,[2,2])):
        got,_=run('carry',j,n,','.join(map(str,bases)))
        B=1;last=-(-n//j);s=F(0)
        for b in bases:
            B*=b;next_value=-(-B*n//j);s+=F(b*last-next_value,B);last=next_value
        check(got['initial_ceiling_gap']==F(-(-n//j))-F(n,j),'initial ceiling gap')
        check(got['carry_sum']==s and got['terminal_gap']==F(last,B)-F(n,j),'mixed radix expansion')
        check(got['identity_error']==0,'carry endpoints')
    for b in (2,3,5,10,36):
        for n in (0,1,b-1,b,b*b-1,b*b,3*b*b,999):
            got,raw=run('polarity',b,n)
            polarity=lambda m:(-1)**((m//(b*b)+(m//b)%b+m%b)//(b-1))
            check(got['polarity']==polarity(n)==1-2*got['square_bit']-2*got['disagreement'],'retained-prefix polarity')
            responses=[int(line.split('response=')[1]) for line in raw.splitlines() if line.startswith('spoke=')]
            check(2*sum(responses)==polarity(n+b-1)-polarity(n)==got['radial_change'],'torsional radial telescoping')
    for M in (2,5,11,17):
        got,raw=run('detail',M);odd=list(range(1,M+1,2))
        G=[[F(gcd(j,k)**2,j*k) for k in odd] for j in odd]
        # Exact constrained quadratic minimizer with a_1=1.
        b=ref.solve(G,[F(int(j==1)) for j in odd]);expected=[x/b[0] for x in b]
        printed=[F(line.split('=')[1]) for line in raw.splitlines() if line.startswith('detail_coefficient=')]
        check(printed==expected and printed[0]==1,'independent gcd-matrix minimization')
    for R,C,E in [(F(0),F(2),F(1)),(F(1),F(2),F(1)),(F(3,2),F(27),F(1,10))]:
        got,_=run('stable-correction',R,C,E);positive=max(F(0),R-E)
        check(got['guaranteed_gain']==positive**2/C,'conditional stable gain')
        check(got['step_size']==(positive/(R*C) if positive else 0),'stable step')
    for t in (1,2,4):
        S=4*t
        for r in (1,3,S+1,2*S+1,4*S-1):
            old,child=coeff(S,r),coeff(2*S,r)
            mass=sum(abs(child[j]-(old[j] if j<len(old) else 0)) for j in range(len(child)))
            for n in (0,r,2*S,3*S+1):
                got,_=run('divisor-family',t,r,n)
                check(got['parent_reading']==field(old,n) and got['child_reading']==field(child,n),'literal fractional clocks')
                check(got['difference']==field(child,n)-field(old,n) and got['changed_reset_mass']==mass<=20,'changed family including terminal coefficient')
                check(got['reciprocal_balance']==0,'reciprocal neutrality')
        old,child=families(S),families(2*S);N=S*S
        got,_=run('divisor-work',t,N)
        shell=sum((field(old,n)**2/F(n*(n+1)) for n in range(S+1,2*S+1)),F(0))
        work=sum(((field(child,n)**2-field(old,n)**2)/F(n*(n+1)) for n in range(2*S+1,N+1)),F(0))-shell
        check(got['parent_shell_energy']==shell,'whole parent shell')
        check(got['finite_head']==work==got['reset_head'],'whole field finite change and joined reset identity')
        check(got['complete_change_lower']==work-F(36*S*S,N+1) and got['complete_change_upper']==work+F(144*S*S,N+1),'two sided complete tail enclosure')
    got,_=run('parent-credit',51)
    check(got['fragment_excess']>F(3,1000) and got['four_reading_lower']<F(1,1000),'published sparse-reading counterexample')
    check(got['fragment_energy']<F(1,100) and got['retained_energy']>F(7,100),'complete retained energy')
    # Direct complete-period C kernel cross-checks the optimized short kernel.
    for j,k in ((2,3),(7,9),(23,32),(63,64)):
        _,raw=run('kernel',j,k,timeout=180)
        intervals=re.findall(r'\[([^,]+), ([^\]]+)\]',raw)
        expected=ref.gram(j,k)
        for lo,hi in intervals:check(D(lo)<=expected<=D(hi),'complete residue period versus short Gram')
    for t in (2,3,4):
        got=run('packet',t,'--json');p,q=packet(t),packet(2*t)
        for key,values in [('coefficients',p),('fine_coefficients',q)]:
            for row in got[key]:ref.contains(row['coefficient'],ref.dec(values[row['clock']]),'classical precursor coefficient')
        pair=lambda a,b:sum((ref.dec(x)*ref.dec(y)*ref.gram(j,k) for j,x in enumerate(a) if j>=2 for k,y in enumerate(b) if k>=2),D(0))
        E=pair(p,p)-D('1.5');E2=pair(q,q)-D('1.5')
        ref.contains(got['energy'],E,'whole packet norm');ref.contains(got['fine_energy'],E2,'whole doubled packet norm');ref.contains(got['signed_work'],E2-E/2,'signed packet work')
        for n in range(1,4*t+1):check(field(p,n)==(-1 if n==1 else 2 if n in (2,3) else 0),'fixed boundary and vanished prefix')
    for q,count in ((2,7),(4,20),(36,1)):
        _,raw=run('copy-cost',q,count);rho=D(1)/D(q).sqrt();expected=[rho,(1+rho)/(1-rho),1+2*sum(((1-D(d)/count)*rho**d for d in range(1,count)),D())]
        for (lo,hi),value in zip(re.findall(r'\[([^,]+), ([^\]]+)\]',raw),expected):check(D(lo)<=value<=D(hi),'sharp universal copy cost')
    for args in [('carry',0,1,'2'),('carry',7,1,'2,'),('detail',1),('polarity',1,0),('stable-correction',1,0,0),('divisor-family',1,2,8),('divisor-work',2,15),('parent-credit',129),('packet',1),('packet',5),('copy-cost','-4294967292',10),('kernel',65,2)]:run(*args,fail=True)
    print(f'PASS native arithmetic: {checks} checks plus {ref.checks} independent interval/coefficients checks; mixed carries, constrained detail, copied masks, divisor families, signed work, parent credit and complete packets.')


if __name__=='__main__':main()

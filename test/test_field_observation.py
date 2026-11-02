#!/usr/bin/env python3
"""Independent exact observations, affine integration and constrained energy."""
import argparse
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import subprocess

checks=0
zero=(F(0),F(0))
def C(x,y=0):return F(x),F(y)
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[0],-a[1]
def sub(a,b):return add(a,neg(b))
def scale(a,b):return a[0]*b,a[1]*b
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def norm(a):return a[0]**2+a[1]**2
def sumc(values):
    out=zero
    for v in values:out=add(out,v)
    return out
def textlist(v):return ','.join(f'{x[0]}:{x[1]}' if isinstance(x,tuple) else str(x) for x in v)
def check(ok,label):
    global checks
    checks+=1
    assert ok,label
def saw(x):return x%1-F(1,2) if x%1 else F(0)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--bin',required=True)
    binary=str(Path(parser.parse_args().bin).resolve())
    def run(*args,fail=False):
        p=subprocess.run([binary,'field-observation',*map(str,args)],capture_output=True,text=True,timeout=15)
        check((p.returncode!=0)==fail,(args,p.stdout,p.stderr))
        if fail:check(not p.stdout,'failed observation emitted result');return
        d={}
        for line in p.stdout.splitlines():
            if '=' in line and ' ' not in line:
                k,v=line.split('=',1);d[k]=tuple(map(F,v.split(':'))) if ':' in v else F(v)
        return d,p.stdout
    clock_sets=[([1],[F(0)],[C(1)]),([1,2],[F(0),F(0)],[C(1),C(-1)]),([2,2,3],[F(1,3),F(1,3),F(1,2)],[C(2,1),C(-1,2),C(F(1,3),-1)])]
    for rs,phases,amps in clock_sets:
        value=lambda x:sumc(scale(a,2*saw(r*x+p)) for r,p,a in zip(rs,phases,amps))
        boundaries=sorted({F(0),F(1)}|{((F(a)-p)/r)%1 for r,p in zip(rs,phases) for a in range(r)})
        integral=F(0)
        for a,b in zip(boundaries,boundaries[1:]):
            h=b-a
            integral+=h*(2*norm(value(a+h/4))-norm(value(a+h/2))+2*norm(value(a+3*h/4)))/3
        for q in (1,3,4,11):
            for theta in (F(0),F(1,2),F(2,7)):
                got,_=run('clocks',q,theta,textlist(rs),textlist(phases),textlist(amps))
                sample=sum((norm(value((F(a)+theta)/q)) for a in range(q)),F(0))/q
                check(got['continuous_energy']==integral and got['sampled_energy']==sample,'three-node exact affine integration and literal grid')
                check(got['defect']==integral-sample==got['point_correction']+got['value_jump']+got['derivative_jump'],'complete complex clock boundary identity')
        # Preserve the shifted grid when averaging refined cosets.
        got,_=run('clocks',15,F(1,2),textlist(rs),textlist(phases),textlist(amps))
        average=sum((run('clocks',5,(F(j)+F(1,2))/3,textlist(rs),textlist(phases),textlist(amps))[0]['defect'] for j in range(3)),F(0))/3
        check(got['defect']==average,'shifted refinement')
    for m in (2,4):
        got,_=run('clocks',6,F(1,2),m,0,1)
        check(got['defect']==(F(1,27) if m==2 else F(7,27)),'shifted dilation example')
    for m in (1,3,17,101):
        for q,expected in ((2*m,F(0)),(2*m+1,F(1,2))):
            got,_=run('harmonics',q,0,f'{m},{-m}','0:-1/2,0:1/2')
            check(got['continuous_energy']==F(1,2) and got['sampled_energy']==expected,'smooth resonance and one additional sample')
        got,_=run('harmonics',2*m,F(1,2),f'{m},{-m}','0:-1/2,0:1/2')
        check(got['sampled_energy']==1 and got['defect']==F(-1,2),'midpoint smooth resonance')
    for left,right,amps,lv,rv in [([F(0)],[F(1,2)],[C(1)],[C(F(1,2))],[C(F(1,2))]),([F(0),F(1,2)],[F(1,2),F(1)],[C(1),C(3)],[C(1),C(1)],[C(1),C(1)]),([F(1,4),F(1,2)],[F(3,4),F(1)],[C(1,2),C(-1,1)],[C(0),C(1)],[C(2,-1),C(0)]),([F(0)],[F(1)],[C(2,3)],[C(1)],[C(1)])]:
        def value(x):
            return sumc(u if x==a else v if x==b or (x==0 and b==1) else z if a<x<b else zero for a,b,z,u,v in zip(left,right,amps,lv,rv))
        points=sorted(set(left+right+[F(0),F(1)]))
        integral=sum(((b-a)*norm(value((a+b)/2)) for a,b in zip(points,points[1:])),F(0))
        for q in (1,3,4,7):
            for theta in (F(0),F(1,2)):
                got,_=run('pulses',q,theta,*map(textlist,[left,right,amps,lv,rv]))
                sample=sum((norm(value((F(a)+theta)/q)) for a in range(q)),F(0))/q
                check(got['continuous_energy']==integral and got['sampled_energy']==sample,'overlapping pulses with actual endpoint readings')
                check(got['point_correction']+got['value_jump']==integral-sample,'pulse trace contribution')
    # Direct three-node integration with unrelated slopes, traces and readings.
    for points,starts,slopes,readings in [([F(0)],[C(0)],[C(1)],[C(0)]),([F(0)],[C(-1)],[C(2)],[C(1)]),([F(0),F(2,5),F(3,4)],[C(1,2),C(-1),C(2,-1)],[C(2,-1),C(1,3),C(-3,2)],[C(0),C(3,-1),C(2)])]:
        def value(x,point=True):
            i=max(i for i,b in enumerate(points) if b<=x)
            return readings[i] if point and x==points[i] else add(starts[i],scale(slopes[i],x-points[i]))
        integral=sum(((b-a)*(2*norm(value(a+(b-a)/4))-norm(value((a+b)/2))+2*norm(value(a+3*(b-a)/4)))/3 for a,b in zip(points,points[1:]+[F(1)])),F(0))
        for q in (1,3,4,7,15):
            for theta in (F(0),F(1,2),F(2,7)):
                got,_=run('segments',q,theta,*map(textlist,[points,starts,slopes,readings]))
                sample=sum((norm(value((F(a)+theta)/q)) for a in range(q)),F(0))/q
                check(got['continuous_energy']==integral and got['sampled_energy']==sample,'independent piecewise affine integral and readings')
                check(got['defect']==sum(got[k] for k in ('point_correction','value_jump','derivative_jump','regular_curvature')),'all boundary terms and regular curvature')
    got,_=run('tail-bound',4,2,3,'-1/10','1/10')
    check(got['sufficient_cutoff']==89,'least envelope cutoff')
    got,_=run('tail-bound',89,2,3,'-1/10')
    check(got['complete_change_lower']==-F(13,90) and got['complete_change_upper']==0,'closed tail sign at sufficient cutoff')
    # Digamma-independent finite sums with a rigorous positive omitted tail.
    import re
    from decimal import Decimal as D, getcontext
    getcontext().prec=60
    for cutoff,cycle in [(0,[C(1)]),(4,[C(1),C(0)]),(2,[C(0),C(-1)]),(17,[C(1,2),C(-2,1),C(0)])]:
        _,raw=run('native-cycle',cutoff,textlist(cycle))
        lo,hi=map(D,re.search(r'complete_energy=\[([^,]+), ([^]]+)\]',raw).groups())
        end=20000
        direct=sum((D(norm(cycle[n%len(cycle)]).numerator)/D(norm(cycle[n%len(cycle)]).denominator)/(D(n)*D(n+1)) for n in range(cutoff+1,end+1)),D())
        upper=D(max(norm(z) for z in cycle).numerator)/D(max(norm(z) for z in cycle).denominator)/D(end+1)
        check(lo<=hi and hi-lo<D('1e-18') and direct<=hi and lo<=direct+upper,'complete periodic tail versus rigorous finite bracketing')
        if len(cycle)==1:check(lo<=D(1)/(cutoff+1)<=hi,'exact constant whole tail')
    for old,new,f,g in [([F(1),F(0),F(2)],[F(0),F(3),F(1)],[C(1,2),C(3),C(-1)],[C(-2,1),C(1,-1),C(1)]),([F(1,2)]*3,[F(2,3)]*3,[C(2),C(3),C(5)],[C(1),C(-1),C(0)])]:
        got,_=run('work',*map(textlist,[old,new,f,g]))
        before=sum(w*norm(z) for w,z in zip(old,f));after=sum(w*norm(add(z,h)) for w,z,h in zip(new,f,g))
        check(got['old_energy']==before and got['new_energy']==after,'common observation space')
        check(got['observation_change']+got['signed_interaction']+got['addition_energy']==after-before,'signed work including changed masses')
    for start in (1,5,17):
        u=[C(1,1),C(-2,3),C(2),C(0,-1),C(3,2)];v=[C(2),C(1,-1),C(-1),C(1,2),C(2,1)]
        got,_=run('native-boundary',start,textlist(u));expected=sumc(scale(z,F(1,n*(n+1))) for n,z in enumerate(u,start))
        check(got['weighted_sum']==expected==add(got['endpoint_terms'],got['reset_terms']),'reciprocal boundary retains both endpoints')
        got,_=run('native-variation',start,textlist(u),textlist(v));expected=sumc(scale(mul(a,b),F(1,n*(n+1))) for n,(a,b) in enumerate(zip(u,v),start))
        check(got['weighted_product']==expected==add(got['upper_endpoint'],got['weighted_variation']),'complex weighted variation')
    weights=[F(1,n*(n+1)) for n in range(5,9)];f=[10,7,0,0];rows=[[56,-80,3,21],[3,-5,0,0]]
    got,_=run('invariants',textlist(weights),textlist(f),*map(textlist,rows))
    check(got['minimum_for_readings']==F(35,158),'complete parent shell constrained minimum')
    transformed=[[C(0,a) for a in rows[0]],[C(b,a) for a,b in zip(rows[0],rows[1])]]
    other,_=run('invariants',textlist(weights),textlist(f),*map(textlist,transformed))
    check(got['minimum_for_readings']==other['minimum_for_readings'],'complex change of reading basis')
    f=[C(1,2),C(-3,1),C(2,-1)];a=[C(1,1),C(2,-1),C(-1,1)];w=[F(1,2),F(2,3),F(3,4)]
    got,_=run('invariants',textlist(w),textlist(f),textlist(a));b=sumc(mul(x,y) for x,y in zip(a,f));cost=sum(norm(x)/mass for x,mass in zip(a,w))
    check(got['minimum_for_readings']==norm(b)/cost,'single complex invariant')
    for sign in (-1,1):
        got,_=run('register','3,4','1,2',f'2,{sign}',textlist([2 if n==10 else 1 for n in range(1,26)]))
        check(got['energy']==(35 if sign<0 else 59)==got['ordered_pair_energy'],'weighted CRT intersections and both cross orientations')
    got,_=run('register','2,4','0,1','1:2,-1:3','1,1,1,1,1,1,1,1')
    check(got['signed_cross_energy']==0,'incompatible residue classes')
    for P in ([F(1),F(2),F(4),F(4)],[F(2),F(-1,2),F(3),F(0),F(-2),F(5,3)]):
        _,raw=run('shells',textlist(P));printed={}
        for line in raw.splitlines():
            parts=dict(item.split('=') for item in line.split())
            if 'cutoff' in parts:
                n=int(parts['cutoff']);check(F(parts['square_prefix'])==sum((n//m*P[m-1] for m in range(1,n+1)),F(0)),'signed shell lifetimes')
            else:printed[int(parts['log_prime'])]=F(parts['coefficient'])
        expected={}
        for p in range(2,len(P)+1):
            if any(p%d==0 for d in range(2,p)):continue
            value=F(0)
            for m,x in enumerate(P,1):
                power=p
                while power<=len(P)//m:value+=x;power*=p
            if value:expected[p]=value
        check(printed==expected,'independent prime-power logarithmic shell transform')
    for args in [('segments',4,0,'1/2','1','0','1'),('segments',4,0,'0,0','1,2','0,0','1,2'),('native-cycle',0,''),('tail-bound',4,-1,2,0),('clocks',0,0,'1','0','1'),('clocks',4,0,'1','0,0','1'),('clocks',4,0,'1/2','0','1'),('clocks',4,1,'1','0','1'),('pulses',4,0,'0','1','1','0','1'),('work','-1','1','1','1'),('invariants','0,1','1,2','1,0'),('invariants','1,1','1,2','1,0','2,0'),('native-boundary',0,'1,2'),('register','2','2','1','1,1'),('shells','1:2,3'),('clocks',4,0,'1','0','1/0')]:run(*args,fail=True)
    print(f'PASS field observations: {checks} independent exact checks; complex clock and pulse grids, endpoints, overlap, observation work, native variation, joint invariants, CRT registers and signed shells.')


if __name__=='__main__':main()

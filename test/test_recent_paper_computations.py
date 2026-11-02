"""Independent finite arithmetic for the seven-paper completion additions.

Production uses Dedekind reciprocity, Euclidean floor sums, Jordan grouping,
CRT character coordinates and completed periods. These oracles use defining
integer sums, Fraction arithmetic and a separate group-extension enumeration.
Numerical comparisons are explicitly toleranced, not formal certificates.
"""
import argparse
import cmath
import csv
import io
import json
import math
from functools import lru_cache
from fractions import Fraction as F
from pathlib import Path
import subprocess

parser=argparse.ArgumentParser()
parser.add_argument('--bin',default='./nfield')
parser.add_argument('--driver',default='test/test_recent_paper_api')
args=parser.parse_args()
BIN=str(Path(args.bin).resolve()); DRIVER=str(Path(args.driver).resolve())
counts={}
def check(condition,group,detail=None):
    assert condition,(group,detail)
    counts[group]=counts.get(group,0)+1
def run(*command,ok=True,driver=False):
    p=subprocess.run([DRIVER if driver else BIN,*map(str,command)],capture_output=True,text=True,timeout=60)
    check((p.returncode==0)==ok,'command status',(command,p.stdout,p.stderr))
    return p.stdout
def fields(*command):
    return dict(line.split('=',1) for line in run(*command).splitlines() if '=' in line)
def exact(command,*parameters):
    return {k:F(v) for k,v in fields('collision-sampling',command,*parameters).items()}
def eq(actual,expected,group):
    for key,value in expected.items(): check(actual[key]==value,group,(key,actual[key],value))
@lru_cache(None)
def dedekind(q,h):
    return F(sum((2*a-q)*(2*(h*a%q)-q) for a in range(1,q) if h*a%q),4*q*q)
def saw(r,q): return F(2*(r%q)-q,2*q) if r%q else F()
def capacity(n):
    return sum((F(math.gcd(r,s)**2,3*r*s) for r in range(1,n+1) for s in range(1,n+1)),F())
def sampled(p):
    q=p*p
    return F(sum(sum(2*(a*r%q)-q for r in range(1,p) if a*r%q)**2 for a in range(q)),q**3)
@lru_cache(None)
def prefix(p,k,x):
    return sum((dedekind(k,p*p*pow(a,-1,k)%k) for a in range(1,x+1) if math.gcd(a,k)==1),F())
def jump(k,s,a):return 2*sum((saw(a*r,k) for r in range(1,s+1)),F())
def correlation(k,s,c):
    return sum((jump(k,s,a)*saw(c*a,k) for a in range(1,k) if math.gcd(a,k)==1),F())
def carrier(p,k):
    n=p-1;m=p*p
    x=sum((n//a*(F(a,k)+F(k,a)) for a in range(k+1,p) if math.gcd(a,k)==1),F())
    r=-8*sum((n//a*dedekind(k,m*pow(a,-1,k)%k) for a in range(k+1,p) if math.gcd(a,k)==1),F()) if k>1 else F()
    alias_a=(n//k)*correlation(k,n%k,m) if k>1 else F()
    alias_c=(n//k)*sum((saw(0,1)+F((m*a%k)**2,k*k)-F(m*a%k,k)+F(1,6) for a in range(1,k) if math.gcd(a,k)==1),F()) if k>1 else F()
    displacement=m%k
    if 2*displacement>k:displacement-=k
    return {'X':x,'reservoir':r,'alias_A':alias_a,'alias_C':alias_c,'displacement':F(displacement)}
def state(p,x,chosen):
    b=sum((prefix(p,k,x) for k in chosen if k<x),F())
    prev=sum((prefix(p,k,x-1) for k in chosen if k<x-1),F())
    return b,b-prev
def convolution(p,x):
    m=p*p
    a=sum((dedekind(m,k*pow(x-k,-1,m)%m) for k in range(1,x)),F())
    c=sum((dedekind(m,k*pow(x-k,-1,m)%m) for k in range(1,x) if math.gcd(k,x)==1),F())
    units=[k for k in range(1,x) if math.gcd(k,x)==1]
    h=sum((F(1,k) for k in units),F())
    e=m*h/(12*x)+(x*h-len(units))/(12*m)-F(len(units),8) if x>=3 else F()
    return {'primitive':c,'full':a,'elementary':e}

run(driver=True)
for m,a,b in [(3,1,1),(5,1,1),(5,1,2),(9,2,2),(15,1,1),(127,35,67)]:
    for power in (2,4,6,12):
        for amplitude in (F(0),F(1),F(-3,2)):
            rows=[[amplitude*(F(k*x%m,m)-F(m-1,2*m)) for x in range(m)] for k in (a,b,a+b)]
            def polarization(f,g,global_energy=False):
                plus=[u+v for u,v in zip(f,g)];minus=[u-v for u,v in zip(f,g)]
                energy=lambda r: (sum((u*u for u in r),F())/m)**2 if global_energy else sum((u**power for u in r),F())/m
                return (energy(plus)-energy(minus))/4
            expected={}
            for nonlocal_energy,prefix_name in [(False,''),(True,'nonlocal_')]:
                values=[polarization(rows[i],rows[j],nonlocal_energy) for i,j in [(0,1),(0,2),(2,1)]]
                expected.update({prefix_name+k:v for k,v in zip(('parent','left','right'),values)})
                expected[prefix_name+'defect']=values[0]-values[1]-values[2]
            actual={k:F(v) for k,v in fields('capacity-generation','measurement',m,a,b,power,str(amplitude)).items()}
            eq(actual,expected,'local and nonlocal measurement oracle')
for q in range(1,33):
    for h in sorted({0,1,q//2,q-1,q+1}):
        eq(exact('dedekind',q,h),{'dedekind':dedekind(q,h)},'Dedekind defining sum')
for n in [0,1,2,3,4,5,9,16,29,50,120,250]:
    eq(exact('capacity',n),{'capacity':capacity(n)},'Jordan versus gcd capacity')
for p in [3,5,7,11,17,29,43]:
    z=exact('inspect',p); cs=[carrier(p,k) for k in range(1,p)]
    x=sum((c['X'] for c in cs),F());r=sum((c['reservoir'] for c in cs),F())
    aa=sum((c['alias_A'] for c in cs),F());cc=F(p-1,6)+sum((c['alias_C'] for c in cs),F())
    eq(z,{'capacity':capacity(p-1),'sampled':sampled(p),'endpoint':F((p-1)**2,p*p),
          'X':x,'reservoir':r,'alias_A':aa,'alias_C':cc,'bridge_error':F(),'alias_error':F()},'sampling and both exact bridges')
    check(z['defect']==z['capacity']-z['sampled']==z['bridge']==z['alias'],'joined sampling identity')
    poles=exact('poles',p)
    diag=4*(p-1)*dedekind(p*p,1)
    off=8*sum((F((p-1)//a)*dedekind(p*p,a*pow(k,-1,p*p)%(p*p)) for a in range(2,p) for k in range(1,a) if math.gcd(k,a)==1),F())
    eq(poles,{'diagonal':diag,'off_diagonal':off,'Ra':F(),'Rk':r,'four_way_error':F(),'energy_error':F()},'four-way poles and modulus-a cancellation')
    check(diag+off==z['sampled']*p*p,'floor versus Dedekind energy')
    if p<=43:
        for k in range(1,p):
            eq(exact('carrier',p,k),carrier(p,k),'individual carrier and square-lock sign')
            if k>=2:
                for X in {0,k-1,k,p-1}:
                    eq(exact('prefix',p,k,X),{'prefix':prefix(p,k,X)},'complete blocks and prefixes')
        for C in {1,p//4 or 1,p//2}:
            terms=[prefix(p,k,(p-1)//h) for k in range(2,p) if 0<abs(carrier(p,k)['displacement'])<=C for h in range(1,(p-1)//(k+1)+1)]
            eq(exact('collar',p,C),{'absolute_mass':F(8,p*p)*sum(map(abs,terms),F()),'signed_mass':F(8,p*p)*sum(terms,F())},'square-lock restricted collar')

# Endpoint of the resource range, compared with the original digit floor
# count, independently of both the production floor-sum and Dedekind paths.
p=251;q=p*p
# Use r=0..p-1 as in the original cell count, not a shifted interval.
floor_mass=sum((p*sum((r*a*(p+1)+a)//q-(r*a*(p+1))//q for r in range(p))-a)**2
               for a in range(1,q) if a%p)
z=exact('inspect',p)
check(z['sampled']==F(floor_mass,q*q),'resource-boundary digit-floor sum')
check(z['bridge_error']==z['alias_error']==0,'resource-boundary joined identities')

for k in range(2,26):
    for s in {0,k//2,k-1}:
        for c in {0,1,2,k-1}:
            eq(exact('correlation',k,s,c),{'correlation':correlation(k,s,c)},'cyclic jump correlation')
for p in [3,5,7,11,17,29]:
    all_k=set(range(2,p-1))
    for x in range(1,p):
        b,f=state(p,x,all_k)
        eq(exact('state',p,x),{'burden':b,'fresh':f},'state at every endpoint')
        eq(exact('convolution',p,x),convolution(p,x),'primitive complementary convolution')
    selections=[all_k,set(),{k for k in all_k if k%2}, {max(all_k)} if all_k else set()]
    for selected in selections:
        z=exact('switching',p,'--carriers',','.join(map(str,sorted(selected))) or 'none')
        n=p-1
        values={x:state(p,x,selected) for x in range(1,p)}
        area=sum((F(n//x-n//(x+1))*values[x][0] for x in range(3,p)),F())
        energy=sum((F(n//x-n//(x+1))*values[x][0]**2 for x in range(3,p)),F())
        currents=[(n//x)*(values[x-1][0]*values[x][1]+values[x][1]**2/2) for x in range(3,p)]
        mean=area/(n//3) if n//3 else F()
        variance=sum((F(n//x-n//(x+1))*(values[x][0]-mean)**2 for x in range(3,p)),F())
        triangle=sum((convolution(p,x)['full'] for x in range(2,p)),F())
        full_reservoir=sum((-carrier(p,k)['reservoir']/8 for k in all_k),F())
        eq(z,{'reservoir':area,'dwell_area':area,'fresh_area':area,'energy':energy,'increment_energy':energy,
              'charge':sum((max(v,F()) for v in currents),F()),'release':sum((max(-v,F()) for v in currents),F()),
              'mean':mean,'coherent_energy':area*mean,'variance':variance,
              'full_triangle':triangle,'full_triangle_bridge':full_reservoir},'selected switching and restored mean')

for q in [2,3,4,5,6,8,9,12,15,16,18,24,25,30,32,45,64]:
    for r in sorted({0,1,2,q//2,q-1}):
        z=fields('collision-sampling','transform',q,r)
        full=sum((complex(dedekind(q,h))*cmath.exp(-2j*math.pi*r*h/q) for h in range(q)),0j)
        unit=sum((complex(dedekind(q,h))*cmath.exp(-2j*math.pi*r*h/q) for h in range(q) if math.gcd(h,q)==1),0j)
        for name,expected in [('full',full),('unit',unit)]:
            actual=complex(float(z[name+'_real']),float(z[name+'_imag']))
            check(abs(actual-expected)<5e-10,'additive transform oracle',(q,r,name))
        check(max(float(z[k]) for k in ['full_error','unit_error','descent_error'])<5e-10,'transform descent and Mobius')
        for X in {0,q-1,q,2*q+1}:
            values=[saw(r*pow(n,-1,q),q) if math.gcd(n,q)==1 else F() for n in range(1,X+1)]
            target={'prefix':sum(values,F()),'harmonic_prefix':sum((v/n for n,v in enumerate(values,1)),F()),'tail_bound':F(q if r%q else 0,2*(X+1))}
            eq(exact('inverse',q,r,X),target,'inverse-residue exact prefix and tail budget')

def independent_characters(m):
    """Extend characters one subgroup generator at a time; no CRT logs."""
    units=[a for a in range(1,m) if math.gcd(a,m)==1];den=len(units)
    def extend(values):
        if len(values)==den:
            yield tuple(values.get(a,-1) for a in range(m));return
        g=next(a for a in units if a not in values)
        powers=[1];v=g
        while v not in values:powers.append(v);v=v*g%m
        for phase in range(den):
            if len(powers)*phase%den!=values[v]:continue
            fresh={a*power%m:(value+j*phase)%den for a,value in values.items() for j,power in enumerate(powers)}
            yield from extend(fresh)
    return den,set(extend({1:0}))

for m in [2,3,4,5,6,8,9,10,12,15,16,18,20,24,25,27,30,32,36,45,49,60,64]:
    den,expected=independent_characters(m)
    table=list(csv.DictReader(io.StringIO(run('table',m,driver=True))))
    phases=[]
    for row in table:
        native_den=int(row['denominator']);ph=[int(v) for v in row['phases'].split(':')]
        canonical=tuple(v*den//native_den if v>=0 else -1 for v in ph)
        phases.append(canonical)
        conductor=next(d for d in range(1,m+1) if m%d==0 and all(canonical[a]==0 for a in range(1,m) if math.gcd(a,m)==1 and a%d==1%d))
        check(int(row['conductor'])==conductor and bool(int(row['odd']))==(canonical[-1]!=0),'exact conductor and parity')
    check(set(phases)==expected and len(phases)==den,'independent full character enumeration',m)
    w=[complex((a%5)-2,(a%3)-1) for a in range(m)]
    encoded=','.join(f'{a}={int(v.real)}:{int(v.imag)}' for a,v in enumerate(w))
    mu=[w[(a-1)%m]-w[a] for a in range(m)]
    response=[-sum((w[x]*complex(saw((x+1)*a,m)-saw(x*a,m)) for x in range(m)),0j) for a in range(m)]
    energy=sum(abs(response[a])**2 for a in range(m) if math.gcd(a,m)==1)
    ledger=fields('boundary-spectrum','inspect',m,'--weights',encoded)
    check(abs(float(ledger['direct_energy'])-energy)<5e-9*max(1,energy),'general boundary energy')
    by_conductor={d:0. for d in range(1,m+1) if m%d==0}
    for ch,row in enumerate(table):
        values=[cmath.exp(2j*math.pi*v/den) if v>=0 else 0j for v in phases[ch]]
        flux=sum((mu[a]*values[a] for a in range(m)),0j)
        transformed=sum((response[a]*values[a].conjugate() for a in range(m)),0j)
        z=fields('boundary-spectrum','channel',m,ch,'--weights',encoded)
        check(abs(complex(float(z['flux_real']),float(z['flux_imag']))-flux)<5e-9,'complex boundary flux')
        check(abs(complex(float(z['transform_real']),float(z['transform_imag']))-transformed)<5e-9,'complex carry transform')
        by_conductor[int(row['conductor'])]+=abs(transformed)**2/den
    for d,val in by_conductor.items():
        check(abs(float(ledger[f'conductor_{d}_energy'])-val)<5e-9*max(1,energy),'nonnegative conductor energy')
    check(max(float(ledger[k]) for k in ['primitive_error','depth_error','inversion_error','unit_reconstruction_error','energy_error','boundary_pairing_error'])<5e-9*max(1,energy),'spectrum identities')

def weight(n):return sum((F(1,2*a*(n-a)*n) for a in range(1,n) if math.gcd(a,n)==1),F())
def harmonic(n):return sum((F(1,k) for k in range(1,n+1)),F())
def mobius(n):
    sign=1;d=2
    while d*d<=n:
        if n%d==0:
            n//=d;sign=-sign
            if n%d==0:return 0
        d+=1
    return -sign if n>1 else sign
def seed_bounds(q,L):
    lo=sum((harmonic(q*k-1)/(q*k)**2 for k in range(1,L+1)),F())
    return lo,lo+(harmonic(q*L)+1)/(q*q*L)
for q,L in [(1,1),(1,40),(2,40),(3,40),(6,20),(12,15),(24,10),(120,2),(240,1)]:
    z={k:F(v) for k,v in fields('capacity-generation','seed',q,L).items()}
    flo,fhi=seed_bounds(q,L)
    eta=sum((weight(q*k) for k in range(1,L+1)),F())
    zlo=sum((F(1,k**3) for k in range(1,L+1)),F());zhi=zlo+F(1,2*L*L)
    delta=F(1)
    for p in range(2,q+1):
        if q%p==0 and all(p%d for d in range(2,math.isqrt(p)+1)):delta*=1-F(1,p**3)
    nlo=nhi=F()
    for d in range(1,q+1):
        if q%d:continue
        lo,hi=seed_bounds(q//d,L);scale=F(mobius(d),d**3)
        nlo+=min(scale*lo,scale*hi);nhi+=max(scale*lo,scale*hi)
    corners=[n/(delta*d) for n in [nlo,nhi] for d in [zlo,zhi]]
    eq(z,{'B0':harmonic(q-1)/q**2,'B0_inverse':sum((F(1,d**3)*weight(q//d) for d in range(1,q+1) if q%d==0),F()),
          'F_lower':flo,'F_upper':fhi,'eta_lower':eta,'eta_upper':eta+fhi-flo,
          'selector_lower':min(corners),'selector_upper':max(corners),'zeta3_lower':zlo,'zeta3_upper':zhi},'exact seed enclosure construction')
    check(max(z['eta_lower'],z['selector_lower'])<=min(z['eta_upper'],z['selector_upper']),'seed selector compatible intervals')
for n in [1,2,3,4,5,6,7,12,17,24,60,120]:
    for lam,coef in [(F(1),[]),(F(2,3),[F(1,7),F(-2,5)]),(F(-1),[F(0),F(1),F(-1,2),F(3,7)])]:
        z={k:F(v) for k,v in fields('capacity-generation','profile',n,str(lam),','.join(map(str,coef)) or 'none').items()}
        row=primitive=grid=F()
        for a in range(1,n):
            t=F(a*(n-a),n*n);h=sum((c*t**j for j,c in enumerate(coef)),F())
            kernel=lam/F(2*a*(n-a)*n)+h/n**3
            row+=kernel;grid+=h
            if math.gcd(a,n)==1:primitive+=kernel
        eq(z,{'primitive':primitive,'row':row,'grid_sum':grid},'symmetric polynomial angular ledger')
for x,L in [(F(1),1),(F(1),16),(F(1,3),7),(F(2,3),12),(F(7,2),9),(F(4),4)]:
    z={k:F(v) for k,v in fields('capacity-generation','lattice',str(x),L).items()}
    lo=sum((1/(F(m*n)*(n+m*x)) for m in range(1,L+1) for n in range(1,L+1)),F())
    eq(z,{'prefix':lo,'upper':lo+2*(harmonic(L)+1)/(L*min(F(1),x)),'reciprocal_prefix':x*lo},'positive lattice and reciprocal prefix')
    longer=sum((1/(F(m*n)*(n+m*x)) for m in range(1,2*L+1) for n in range(1,2*L+1)),F())
    check(lo<=longer<=z['upper'],'finite tail enclosure sanity check')

invalid=[('collision-sampling','inspect','7junk'),('collision-sampling','inspect',9),('collision-sampling','inspect',257),
 ('collision-sampling','capacity',251),('collision-sampling','prefix',7,7,1),('collision-sampling','inverse',7,1,4097),
 ('collision-sampling','switching',7,'--carriers','2,2'),('collision-sampling','switching',7,'--carriers','6'),
 ('collision-sampling','switching',7,'--carriers','2,'),('collision-sampling','correlation',513,1,1),
 ('collision-sampling','dedekind',0,0),('collision-sampling','inspect',7,'extra'),('collision-sampling','collar',7,4),
 ('boundary-spectrum','inspect',513,'--support','0'),('boundary-spectrum','inspect',12,'--support','12'),
 ('boundary-spectrum','inspect',12,'--support','1,1'),('boundary-spectrum','inspect',12,'--weights','0=nan:0'),
 ('boundary-spectrum','inspect',12,'--weights','0=1001:0'),('boundary-spectrum','channel',12,4,'--support','0'),
 ('boundary-spectrum','inspect','12junk','--support','0'),('boundary-spectrum','inspect',12,'--weights','0=1'),
 ('boundary-spectrum','inspect',12,'--weights','0=1:0,0=2:0')]
invalid += [('capacity-generation','measurement',5,1,1,3,1),
 ('capacity-generation','measurement',4,1,1,2,1),('capacity-generation','measurement',5,1,4,2,1),
 ('capacity-generation','measurement',5,1,1,2,'1/0'),
 ('capacity-generation','seed',0,5),('capacity-generation','seed',2,121),
 ('capacity-generation','profile',121,1,'none'),('capacity-generation','profile',7,'1/0','none'),
 ('capacity-generation','profile',7,1,'1,'),('capacity-generation','profile',7,1,'1/0'),
 ('capacity-generation','lattice',0,4),('capacity-generation','lattice','-1/2',4),
 ('capacity-generation','lattice',1,65),('capacity-generation','lattice','1/0',4)]
for command in invalid:run(*command,ok=False)
for obj,actions in [('collision-sampling','inspect carrier poles collar prefix correlation state switching convolution capacity dedekind transform inverse verify'),('boundary-spectrum','inspect channel verify')]:
    check(obj in run('__complete').splitlines(),'registry')
    check(obj in run('__complete','help').splitlines(),'help registry')
    check(obj in run('__complete','verify').splitlines(),'verifier registry')
    check(set(actions.split())<=set(run('__complete',obj).splitlines()),'action completion')
    check('0 failures' in run('verify',obj),'native verifier')
    check(run('help',obj)==run(obj,'--help'),'focused help')
print(json.dumps({'passed':True,'checks':counts,'total':sum(counts.values()),
 'boundary':'Exact finite identities and explicit numerical comparisons. No infinite theorem or open estimate certified.'},indent=2))

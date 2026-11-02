"""Independent finite oracles for the generating paper's native object.

Integer cell counts, direct covariance, primitive-pair sums, finite differences,
and rational formal-log coefficients. No asymptotic conclusion is tested here.
"""
import csv, io, json, math, subprocess
from fractions import Fraction as F
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
BIN=ROOT/'nfield'
counts={}
def case(group):counts[group]=counts.get(group,0)+1
def run(*args,ok=True):
    p=subprocess.run([str(BIN),*map(str,args)],capture_output=True,text=True,timeout=60)
    assert (p.returncode==0)==ok,(args,p.stdout,p.stderr)
    return p.stdout
def rows(*args):return list(csv.DictReader(io.StringIO(run('capacity-generation',*args))))
def mu(n):
    primes=[]
    for d in range(2,n+1):
        if n%d==0 and all(d%p for p in primes):
            if n%(d*d)==0:return 0
            primes.append(d)
    return (-1)**len(primes)
def divisors(n):return [d for d in range(1,n+1) if n%d==0]
def weight(k):return sum((F(1,2*a*(k-a)*k) for a in range(1,k) if math.gcd(a,k)==1),F())
def cap(n):return sum((F(math.gcd(r,s)**2,3*r*s) for r in range(1,n+1) for s in range(1,n+1)),F())
def covariance(x,y):return sum((a*b for a,b in zip(x,y)),F())/len(x)

for base,lag in [(2,1),(2,4),(3,1),(3,3),(4,2),(5,2),(6,2),(7,1),(10,2),(15,1),(16,1)]:
    q=base**lag;m=base*q
    cells=[n for n in range(m) if n//q==n%base]
    assert len(cells)==q
    for record in rows('source',base,lag):
        phase=int(record['phase']);a=((1-q)*phase)%m
        # The finite count is computed from each cell's two endpoints.
        response=sum(((n+1)*a//m-n*a//m for n in cells),0)-F(a,base)
        assert F(record['cell_response'])==response==F(record['affine_sample'])
        case('cell phases')

for m in range(3,26,2):
    for a in range(1,m):
        for b in range(1,m):
            if any(math.gcd(k,m)!=1 for k in [a,b,a+b]):continue
            U=lambda r:[F((r*x)%m,m)-F(m-1,2*m) for x in range(m)]
            midpoint=lambda r:[F((r*x)%m,m)-F(1,2) if r*x%m else F() for x in range(m)]
            u,v,w=U(a),U(b),U(a+b)
            record=rows('carry',m,a,b)[0]
            assert F(record['parent'])==covariance(u,v)
            assert F(record['left'])==covariance(u,w)
            assert F(record['right'])==covariance(w,v)
            assert covariance(u,v)==covariance(u,w)+covariance(w,v)
            k=[F(((a*x)%m+(b*x)%m)//m) for x in range(m)]
            mean=sum(k,F())/m
            variance=sum(((v-mean)**2 for v in k),F())/m
            assert F(record['carry_variance'])==variance==3*covariance(u,u)
            u,v,w=midpoint(a),midpoint(b),midpoint(a+b)
            assert F(record['midpoint_defect'])==covariance(u,v)-covariance(u,w)-covariance(w,v)==F(m-1,4*m*m)
            case('unit triples')

for rec in rows('ledger',80):
    n=int(rec['n']);assert F(rec['capacity'])==cap(n)
    assert F(rec['weight'])==weight(n)==F(rec['recovered_weight'])
    assert F(rec['unprimitive_row'])==sum((F(1,d**3)*weight(n//d) for d in divisors(n)),F())
    case('capacity and primitive recovery')

for a in range(1,17):
    for b in range(1,17):
        if math.gcd(a,b)>1:continue
        z=rows('refine',a,b)[0]
        u,v,h=map(int,[z['left_numerator'],z['right_numerator'],z['mediant_numerator']])
        assert a*v-b*u==1 and 0<=F(u,a)<F(v,b)<=1 and u+v==h
        assert F(z['parent_mass'])==F(z['left_mass'])+F(z['right_mass'])==F(1,2*a*b)
        case('Farey edges')

for r,s in [(7,11),(13,17),(19,23),(31,37)]:
    size=2*s
    records=rows('control',r,s,size)
    eps=F(1,8*s**3)
    dm={int(z['n']):F(z['delta_mass']) for z in records}
    for z in records:
        n=int(z['n'])
        expected=eps*((F(mu(n//r),(n//r)**3) if n%r==0 else F())-
                      (F(mu(n//s),(n//s)**3) if n%s==0 else F()))
        assert dm[n]==expected
        deltaB=sum((F(1,d**3)*dm[n//d] for d in divisors(n)),F())
        assert deltaB==F(z['delta_row'])==eps*((n==r)-(n==s))
        assert F(z['delta_capacity'])==F(2,3)*sum((k*dm[k]*(n//k) for k in range(2,n+1)),F())
        assert weight(n)+dm[n]>0 if n>=2 else dm[n]==0
        if n<r:assert F(z['delta_capacity'])==0
        case('smooth row and mass controls')
    current=rows('current',r-1,r,s)
    for z in current:
        n,p=int(z['n']),int(z['prime']);k=n;exponent=0
        while k%p==0:exponent+=1;k//=p
        expected=F(k==1)
        if n==r-1:expected+=n*eps*r*r*exponent
        assert F(z['log_coefficient'])==expected
        case('first changed formal log coefficients')

record={(int(z['n']),int(z['prime'])):F(z['log_coefficient']) for z in rows('current',80)}
for n in range(1,81):
    for p in range(2,n+1):
        if len(divisors(p))!=2:continue
        k=n
        while k%p==0:k//=p
        assert record.get((n,p),F())==F(k==1)
        case('prime powers and zero coefficients')

# A finite counterexample for a pointwise quartic measurement is not the
# theorem forcing quadratic density over unbounded tests.
f=[-2,-1,0,1,2];g=[-2,0,2,-1,1]
def polar(f,g,power):return sum((F((a+b)**power-(a-b)**power,20) for a,b in zip(f,g)),F())
assert polar(f,f,2)-2*polar(f,g,2)==0
assert polar(f,f,4)-2*polar(f,g,4)!=0
case('local power control')
for args in [('carry',4,1,1),('carry',9,1,2),('source',64,3),('source',5,1,25),
             ('ledger',0),('ledger',121),('control',7,9,20),('current',10,7,14),
             ('current','10junk'),('source',2,0),('refine',2,4),('unknown',)]:
    run('capacity-generation',*args,ok=False);case('input rejection')
assert 'capacity-generation' in run('__complete').splitlines()
assert 'capacity-generation' in run('__complete','help').splitlines()
assert 'capacity-generation' in run('__complete','verify').splitlines()
assert set(['source','carry','ledger','refine','control','current','verify'])<=set(run('__complete','capacity-generation').splitlines())
assert '4096' in run('help','capacity-generation')
case('registry and help')
print(json.dumps({'status':'passed','cases':counts,'total':sum(counts.values()),
                  'boundary':'Exact finite and negative-control checks. No infinite theorem certified.'},indent=2))

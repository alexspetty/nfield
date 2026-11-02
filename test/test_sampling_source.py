#!/usr/bin/env python3
"""Independent finite grids, literal counting, reciprocity paths and prefix words."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from math import gcd
from pathlib import Path
import subprocess

checks = 0


def check(ok, label):
    global checks
    checks += 1
    assert ok, label


def saw(x):
    r = x % 1
    return r-F(1, 2) if r else F(0)


@lru_cache(None)
def ded(h, k):
    return sum((saw(F(a, k))*saw(F(h*a, k)) for a in range(k)), F(0))


def count(Q, k, L):
    # Count the original positive and negative residue occurrences, not the
    # implementation's two indicator comparisons after complete blocks cancel.
    return sum((j-Q) % k == 0 for j in range(1, L+1))-sum((j+Q) % k == 0 for j in range(1, L+1))


def source(N, k, Q):
    return sum(count(Q, k, N//r) for r in range(1, N//k+1))


def words(cap):
    rows = {}
    def visit(A, B, C, E, digits):
        if digits:
            check((A, B) not in rows, 'unique forward-generated top row')
            rows[A, B] = (C, E, digits)
        for sign in (-1, 1):
            for m in range(3 if sign < 0 else 2, cap+1):
                if A*m+B > cap:
                    break
                visit(A*m+B, sign*A, C*m+E, sign*C, digits+[(m, sign)])
    visit(1, 0, 0, 1, [])
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bin', required=True)
    binary = str(Path(parser.parse_args().bin).resolve())
    def run(*args, fail=False):
        p = subprocess.run([binary, 'collision-sampling', *map(str, args)], text=True, capture_output=True, timeout=15)
        check((p.returncode != 0) == fail, (args, p.stdout, p.stderr))
        if fail:
            check(not p.stdout, ('failed command produced data', args))
            return
        data = {}
        for line in p.stdout.splitlines():
            if '=' in line and ' ' not in line:
                key, value = line.split('=', 1)
                data[key] = F(value)
        return data, p.stdout
    for N in (1, 2, 4, 7, 12):
        J = sum((F(gcd(j,k)**2, 3*j*k) for j in range(1,N+1) for k in range(1,N+1)), F(0))
        for q in (1, 3, 11, 25):
            for theta in (F(0), F(1,2), F(2,3)):
                got, _ = run('grid', N, q, theta)
                sampled = sum((sum(2*saw(j*(F(a)+theta)/q) for j in range(1,N+1))**2 for a in range(q)), F(0))/q
                resets = {F(a,k) for k in range(1,N+1) for a in range(k)}
                point = sum((sum((j*b)%1 == 0 for j in range(1,N+1))**2 for b in resets if (q*b-theta)%1 == 0), F(0))/q
                check(got['capacity'] == J and got['sampled'] == sampled, ('literal grid',N,q,theta))
                check(got['defect'] == J-sampled and got['point'] == point, 'sampled reset contribution')
                check(got['identity_error'] == 0 and got['point']+got['jump']+got['curvature'] == J-sampled, 'complete boundary identity')
    for N,k in ((1,5),(10,2),(20,7),(30,11),(40,9)):
        cells = [source(N,k,a) for a in range(k)]
        for Q in (-100,-1,0,1,19):
            got,_ = run('source',N,k,Q)
            check(got['source'] == source(N,k,Q), 'literal signed source')
            check(got['residue_sum'] == sum(cells) == 0, 'source mean')
            check(got['absolute_max'] == max(map(abs,cells)), 'source amplitude')
            check(got['cyclic_variation'] == sum(abs(cells[i]-cells[i-1]) for i in range(k)), 'source variation')
    for p in (3,5,11,23,43,61):
        N=p-1
        A=sum((source(N,k,p*p*h)*ded(h,k) for k in range(2,N+1) for h in range(1,k) if gcd(h,k)==1),F(0))
        for H in sorted({1,2,N//2,N}):
            got,_=run('decomposition',p,H)
            check(got['source_sum']==A, 'original Dedekind source')
            expected=[F(0) for _ in range(5)]
            for k in range(2,N+1):
                for c in range(1,(k+1)//2):
                    if gcd(c,k)!=1: continue
                    weight=2*source(N,k,p*p*pow(c,-1,k))
                    if c<=H:
                        expected[0]+=weight*ded(c,k)
                        continue
                    expected[1]+=weight*(ded(c,k)+ded(k,c))
                    d=min(k%c,c-k%c)
                    if d<=H or 2*d==c:
                        expected[2]-=weight*ded(k,c)
                        continue
                    u,v,orientation=k,c,1
                    while True:
                        r=u%v
                        if min(r,v-r)<=H or 2*r==v: break
                        sign=1 if 2*r<v else -1
                        next_v=r if sign>0 else v-r
                        # Dedekind differences telescope independently of the
                        # implementation's rational reciprocity correction.
                        next_orientation=-sign*orientation
                        expected[3]-=weight*(orientation*ded(u,v)-next_orientation*ded(v,next_v))
                        u,v,orientation=v,next_v,next_orientation
                    expected[4]-=weight*orientation*ded(u,v)
            check([got[k] for k in ('small_pairs','first_cost','small_remainders','stopped_cost','terminal')]==expected, ('stopped split',p,H))
    for k,c,H in ((7,2,1),(43,18,1),(101,43,2),(251,96,1),(17,7,8)):
        got,_=run('descent',k,c,H)
        check(got['cost']+got['terminal']==ded(k,c)==got['dedekind'], 'stopped path')
    rows=words(36)
    for (A,B),(C,E,digits) in list(rows.items())[::9]:
        got,raw=run('prefix-word',A,B)
        check((got['C'],got['E'],got['determinant'])==(C,E,A*E-B*C), 'forward matrix')
        printed=[tuple(int(part.split('=')[1]) for part in line.split()) for line in raw.splitlines() if line.startswith('digit=')]
        check(printed==digits, 'backward word reconstructs forward word')
        if len(digits)>=2:
            got,_=run('fold',A,B,7,2,121,40)
            k=A*7+B*2;c=C*7+E*2
            check(got['original_count']==(A*E-B*C)*count(121*pow(c,-1,k),k,40)==got['folded_count'], 'orientation fold')
    for L,Q,K,u,e in ((100,121,2,5,1),(250,529,4,9,2),(512,3721,8,7,3)):
        got,_=run('folded-source',L,Q,K,u,e)
        total=0;terms=0
        for (A,B),(C,E,digits) in words(2*K-1).items():
            k=A*u+B*e;c=C*u+E*e
            if A<K or len(digits)<2 or k>L: continue
            total+=(A*E-B*C)*count(Q*pow(c,-1,k),k,L);terms+=1
        check(got['joined_source']==total and got['primitive_prefixes']==terms, 'joined source from forward words')
    for Q,X,Y in ((25,4,4),(49,6,5),(26,7,9)):
        for parity in range(3):
            got,_=run('rectangle',Q,X,Y,parity)
            value=2*sum((sum((saw(F(j*h,k))*saw(F(Q*h,k)) for h in range(k)),F(0)) for k in range(1,X+1) for j in range(1,Y+1) if (parity!=1 or k%2) and (parity!=2 or j%2)),F(0))
            check(got['source_rectangle']==value, 'nonprimitive/parity rectangle')
    for k in (1,2,7,24,61):
        got,_=run('dedekind-mass',k)
        check(got['absolute_mass']==sum(abs(ded(h,k)) for h in range(k) if gcd(h,k)==1)<=got['mass_bound'], 'absolute Dedekind mass')
    for p in (3,5,11,43):
        got,_=run('cubic',p);grid,_=run('grid',p-1,p*p,0)
        check(got['constant_eigenvalue_change']==-grid['defect'], 'constant cubic correction')
        check(got['transverse_eigenvalue_change']==grid['defect']/2-F(3*(p-1),2*p*p)+F(p-1,p**4), 'transverse cubic correction')
    for gamma,X,beta,first,last in [(F(0),F(121),F(0),2,12),(F(1,3),F(-49),F(-1,3),3,20),(F(-7,5),F(13,2),F(2),5,14)]:
        got,_=run('phase-sum',gamma,X,beta,first,last)
        expected=sum(((gamma+X/(n+beta))%1-F(1,2) for n in range(first,last+1)),F(0))
        check(got['literal_sawtooth_sum']==expected,'literal reciprocal phase including integer endpoints')
    for N,k,Q in [(24,7,625),(10,6,121),(12,5,24)]:
        weights=[F(0)]+[F((-1)**j*j,j+1) for j in range(1,k)]
        got,_=run('completion',N,k,Q,','.join(map(str,weights)))
        expected=sum((weights[c]*source(N,k,Q*pow(c,-1,k)) for c in range(1,k) if gcd(c,k)==1),F(0))
        check(got['completed_source']==expected,'completion retains original inverse and nonunit exclusions')
        check(got['cyclic_variation']==sum(abs(weights[c]-weights[c-1]) for c in range(k)),'completion cyclic variation')
    for Q,a,b in [(121,3,4),(49,2,5),(121,6,10)]:
        got,_=run('kernel',Q,a,b)
        value=ded(a*pow(Q,-1,b),b)+ded(b*pow(Q,-1,a),a)
        check(got['boundary_kernel']==value,'two-denominator arithmetic kernel')
    for Q,N in ((49,6),(121,10)):
        _,raw=run('shells',Q,N)
        rows=[dict(part.split('=') for part in line.split()) for line in raw.splitlines()]
        kernel=lambda a,b:ded(a*pow(Q,-1,b),b)+ded(b*pow(Q,-1,a),a)
        for row in rows:
            if 'cutoff' in row:
                m=int(row['cutoff'])
                check(F(row['primitive_shell'])==sum((kernel(a,b) for a in range(1,m+1) for b in range(1,m+1) if max(a,b)==m and gcd(a,b)==1),F(0)),'ordered primitive pairs')
                check(F(row['square_prefix'])==sum((kernel(a,b) for a in range(1,m+1) for b in range(1,m+1)),F(0)),'fixed-carrier square prefix')
        if Q==121:check(rows[-1]=={'log_prime':'2','coefficient':'1/4'},'published finite logarithmic example')
    for p in (257,509,997):
        got,_=run('interior',p);a=int(got['left_index']);b=int(got['right_index'])
        check(got['absolute_mean_zero_rayleigh']==ded(1,b)+ded(2*(p-int(a**.5)),a)>=F(p,64),'mean-zero interior witness')
    for a,b in ((5,7),(8,13),(11,18)):
        got,_=run('reciprocal',a,b,-3)
        check(got['original_phase']-got['adjacent_phase']-got['correction']==got['integer_phase_difference'] and got['integer_phase_difference'].denominator==1,'adjacent reciprocal phase')
    for args in [('grid',0,10,0),('grid',121,10,0),('grid',3,0,0),('grid',3,7,'1/0'),('grid',3,7,1),('source',10,0,2),('decomposition',9,2),('decomposition',7,0),('descent',8,4,1),('prefix-word',8,7),('prefix-word',6,-2),('fold',8,-3,4,2,25,10),('rectangle',7,5,3,3),('cubic',4)]:
        run(*args,fail=True)
    print(f'PASS signed sampling sources: {checks} independent checks; literal grids, resets, original counts, stopped costs, forward words, signed folds, parity and cubic corrections.')


if __name__=='__main__': main()
